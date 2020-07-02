use crate::chain::tendermint::TendermintChain;
use crate::chain_event::ChainEvent;
use crate::config::Config;
use crate::query::ibc_query;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics02_client::query::{ConsensusStateResponse, QueryClientConsensusState};
use relayer_modules::ics03_connection::query::{ConnectionResponse, QueryConnection};
use relayer_modules::ics07_tendermint::consensus_state::ConsensusState;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};
use tendermint::block::Height;
use tokio::sync::mpsc::{Receiver, Sender};
use tracing::info;

/// The Querier handles query requests from the event handler.
pub struct ChainQueryHandler {
    config: Config,
    /// Channel where query requests are received from relayer.
    query_request_rx: Receiver<ChainQueryRequestParams>,
    /// Channel where query responses are sent to the relayer.
    query_response_tx: Sender<ChainQueryResponse>,
}

impl ChainQueryHandler {
    /// Constructor for the Query Handler
    pub fn new(
        config: Config,
        query_request_rx: Receiver<ChainQueryRequestParams>,
        query_response_tx: Sender<ChainQueryResponse>,
    ) -> Self {
        ChainQueryHandler {
            config,
            query_request_rx,
            query_response_tx,
        }
    }

    ///Query Handler loop
    pub async fn run(&mut self) {
        info!("running IBC Querier Handler");

        loop {
            if let Some(query) = self.query_request_rx.recv().await {
                let response = self.chain_ibc_query(&query).await;

                let _res = self
                    .query_response_tx
                    .send(ChainQueryResponse {
                        trigger: query,
                        response,
                    })
                    .await;
            }
        }
    }

    pub async fn chain_ibc_query(&mut self, query: &ChainQueryRequestParams) -> QueryResponse {
        let chain = &TendermintChain::from_config(
            self.config
                .chains
                .iter()
                .find(|c| c.id == query.chain)
                .unwrap()
                .clone(),
        )
        .unwrap();

        match query.request.clone() {
            ChainQueryRequest::ClientConsensusParams(q) => {
                let response = ibc_query(
                    chain,
                    QueryClientConsensusState::new(
                        u64::from(query.chain_height),
                        q.client_id,
                        u64::from(q.consensus_height),
                        query.prove,
                    ),
                )
                .await
                .unwrap();
                QueryResponse::ClientConsensusState(response)
            }
            ChainQueryRequest::ConnectionParams(q) => {
                let response = ibc_query(
                    chain,
                    QueryConnection::new(
                        u64::from(query.chain_height),
                        q.connection_id,
                        query.prove,
                    ),
                )
                .await
                .unwrap();
                QueryResponse::Connection(response)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ChainQueryRequestParams {
    pub(crate) chain: ChainId,
    pub chain_height: Height,
    pub prove: bool,
    pub request: ChainQueryRequest,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ChainQueryRequest {
    ClientConsensusParams(ClientConsensusParams),
    ConnectionParams(ConnectionParams),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClientConsensusParams {
    pub client_id: ClientId,
    pub consensus_height: Height,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConnectionParams {
    pub connection_id: ConnectionId,
}

#[derive(Debug, Clone)]
pub enum QueryResponse {
    ClientConsensusState(ConsensusStateResponse<ConsensusState>),
    Connection(ConnectionResponse),
}

#[derive(Debug, Clone)]
pub struct ChainQueryResponse {
    pub trigger: ChainQueryRequestParams,
    pub response: QueryResponse,
}

pub(crate) fn valid_query_response(
    response: &ChainQueryResponse,
    queries: &[ChainQueryRequestParams],
) -> bool {
    for query in queries {
        if *query == response.trigger {
            return true;
        }
    }
    false
}

pub fn chain_query_consensus_state_request(
    chain: ChainId,
    chain_height: Height,
    client_id: ClientId,
    consensus_height: Height,
    prove: bool,
) -> ChainQueryRequestParams {
    let p = ClientConsensusParams {
        client_id,
        consensus_height,
    };
    ChainQueryRequestParams {
        chain,
        chain_height,
        prove,
        request: ChainQueryRequest::ClientConsensusParams(p),
    }
}

pub fn chain_query_object_request(
    event: &ChainEvent,
    prove: bool,
) -> Result<ChainQueryRequestParams, BoxError> {
    Ok(ChainQueryRequestParams {
        chain: event.trigger_chain,
        chain_height: event.chain_height,
        prove,
        request: event.trigger_object.new_query_request()?,
    })
}

pub fn chain_query_flipped_object_request(
    dest_chain: ChainId,
    event: &ChainEvent,
    prove: bool,
) -> Result<ChainQueryRequestParams, BoxError> {
    let flipped = event.trigger_object.flipped()?;

    Ok(ChainQueryRequestParams {
        chain: dest_chain,
        chain_height: event.chain_height,
        prove,
        request: flipped.new_query_request()?,
    })
}
