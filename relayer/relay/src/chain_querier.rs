use crate::chain::tendermint::TendermintChain;
use crate::config::Config;
use crate::event_handler::BuilderTrigger;
use crate::query::connection::query_connection;
use ::tendermint::chain::Id as ChainId;
use relayer_modules::ics02_client::query::ConsensusStateResponse;
use relayer_modules::ics03_connection::query::ConnectionResponse;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};
use tendermint::block::Height;
use tokio::sync::mpsc::{Receiver, Sender};
use tracing::info;

// event_handler to Chain for queries
#[derive(Debug, Clone)]
pub struct ChainQuery {
    // this will change
    pub trigger: BuilderTrigger,
    pub request: QueryRequest,
}

#[derive(Debug, Clone)]
pub enum QueryRequest {
    ClientConsensusRequest(QueryClientConsensus),
    ConnectionEndRequest(QueryConnectionEnd),
}

#[derive(Debug, Clone)]
pub struct QueryClientConsensus {
    chain: ChainId,
    chain_height: Height,
    client_id: ClientId,
    prove: bool,
}

impl QueryClientConsensus {
    pub fn new(chain: ChainId, chain_height: Height, client_id: ClientId, prove: bool) -> Self {
        QueryClientConsensus {
            chain,
            chain_height,
            client_id,
            prove,
        }
    }
}

#[derive(Debug, Clone)]
pub struct QueryConnectionEnd {
    pub chain: ChainId,
    pub chain_height: Height,
    pub connection_id: ConnectionId,
    pub prove: bool,
}

impl QueryConnectionEnd {
    pub fn new(
        chain: ChainId,
        chain_height: Height,
        connection_id: ConnectionId,
        prove: bool,
    ) -> Self {
        QueryConnectionEnd {
            chain,
            chain_height,
            connection_id,
            prove,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ChainQuerierResponse<CS> {
    pub from_chain: ChainId,
    pub trigger: BuilderTrigger,
    pub response: QueryResponse<CS>,
}

#[derive(Debug, Clone)]
pub enum QueryResponse<CS> {
    ConsensusStateResponse(ConsensusStateResponse<CS>),
    ConnectionEndResponse(ConnectionResponse),
}

fn matching_req_resp<CS>(req: &QueryRequest, resp: &QueryResponse<CS>) -> bool {
    match (req, resp) {
        (
            QueryRequest::ClientConsensusRequest(cons_req),
            QueryResponse::ConsensusStateResponse(cons),
        ) => Height(cons.proof_height) == cons_req.chain_height,

        (
            QueryRequest::ConnectionEndRequest(conn_req),
            QueryResponse::ConnectionEndResponse(conn),
        ) => Height(conn.proof_height) == conn_req.chain_height,

        (_, _) => false,
    }
}

pub(crate) fn valid_query_response<CS>(
    response: &QueryResponse<CS>,
    queries: &[QueryRequest],
) -> bool {
    for req in queries {
        if !matching_req_resp(req, &response) {
            continue;
        }
        return true;
    }
    false
}

/// The Querier handles IBC events from the monitors.
pub struct ChainQueryHandler<CS> {
    config: Config,
    /// Channel where query requests are received from relayer.
    query_request_rx: Receiver<ChainQuery>,
    /// Channel where query responses are sent to the relayer.
    query_response_tx: Sender<ChainQuerierResponse<CS>>,
}

impl<CS> ChainQueryHandler<CS> {
    /// Constructor for the Query Handler
    pub fn new(
        config: Config,
        query_request_rx: Receiver<ChainQuery>,
        query_response_tx: Sender<ChainQuerierResponse<CS>>,
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
                let obj = query.clone().trigger;
                let request = query.clone().request;

                match request {
                    QueryRequest::ConnectionEndRequest(query) => {
                        let response = query_connection(
                            &TendermintChain::from_config(
                                self.config
                                    .chains
                                    .iter()
                                    .find(|c| c.id == query.chain)
                                    .unwrap()
                                    .clone(),
                            )
                            .unwrap(),
                            u64::from(query.chain_height),
                            query.connection_id.clone(),
                            query.prove,
                        )
                        .await
                        .unwrap();

                        let _res = self
                            .query_response_tx
                            .send(ChainQuerierResponse {
                                from_chain: query.chain,
                                trigger: obj,
                                response: QueryResponse::ConnectionEndResponse(response),
                            })
                            .await;
                    }
                    _ => {}
                }
            }
        }
    }
}
