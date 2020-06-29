use relayer_modules::events::IBCEvent;
use tokio::sync::mpsc::{Receiver, Sender};

use crate::chain_event::{BuilderEvent, ChainEvent};
use crate::chain_querier::{ChainQueryRequest, ChainQueryResponse};
use crate::config::Config;
use crate::light_client_querier::{LightClientQuerierResponse, LightClientQuery};
use crate::message_builder::BuilderRequests;
use crate::relayer_state::{BuilderObject, BuilderTrigger, RelayerState};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::query::{IbcQuery, IbcResponse};
use tracing::{debug, info};

pub enum RelayerEvent<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    ChainEvent(ChainEvent<O>),
    QueryEvent(ChainQueryResponse<O, Q>),
    LightClientEvent(LightClientQuerierResponse<O>),
}

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    /// If true the handler processes event and attempts to relay,
    /// otherwise it only dumps the events.
    relay: bool,
    config: Config,

    /// Channel where events from the different chains are received
    chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,

    /// Channel where query requests are sent
    /// TODO - make one querier per chain
    query_request_tx: Sender<ChainQueryRequest<O, Q>>,
    /// Channel where query responses are received
    query_response_rx: Receiver<ChainQueryResponse<O, Q>>,

    light_client_request_tx: Sender<LightClientQuery<O>>,
    light_client_response_rx: Receiver<LightClientQuerierResponse<O>>,

    /// Relayer state, updated by the different events on _rx channels
    relayer_state: RelayerState<O, Q>,
}

impl<O: 'static, Q: 'static> EventHandler<O, Q>
where
    O: BuilderObject + std::marker::Sync,
    Q: IbcQuery + std::marker::Sync,
{
    /// Constructor for the Event Handler
    pub fn new(
        relay: bool,
        config: &Config,
        chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,
        query_request_tx: Sender<ChainQueryRequest<O, Q>>,
        query_response_rx: Receiver<ChainQueryResponse<O, Q>>,
        light_client_request_tx: Sender<LightClientQuery<O>>,
        light_client_response_rx: Receiver<LightClientQuerierResponse<O>>,
    ) -> Self {
        EventHandler {
            relay,
            config: config.clone(),
            chain_ev_rx,
            query_request_tx,
            query_response_rx,
            light_client_request_tx,
            light_client_response_rx,
            relayer_state: RelayerState::new(config.clone()),
        }
    }

    ///Event Handler loop
    pub async fn run(&mut self) {
        info!("running IBC Event Handler");
        loop {
            if let Some(events) = self.chain_ev_rx.recv().await {
                for event in events.1 {
                    if !self.relay {
                        info!("Chain {} pushed {}", events.0, event.to_json());
                        //continue;
                    }
                    let _handle = self
                        .event_handler(RelayerEvent::ChainEvent(
                            ChainEvent::new_from_ibc_event(events.0, event).unwrap(),
                        ))
                        .await;
                }
            }
            if let Some(event) = self.query_response_rx.recv().await {
                let _handle = self.event_handler(RelayerEvent::QueryEvent(event));
            }
        }
    }

    async fn event_handler(&mut self, event: RelayerEvent<O, Q>)
    where
        O: BuilderObject,
        Q: IbcQuery,
    {
        match event {
            RelayerEvent::ChainEvent(chain_event) => {
                match self.ibc_event_handler(chain_event).await {
                    Ok(()) => debug!("Successful handling of event\n"),
                    Err(e) => debug!("Handling of event returned {}\n", e),
                }
            }
            RelayerEvent::QueryEvent(response) => match self.query_response_handler(&response).await
            {
                Ok(()) => debug!("Successful handling of query response\n"),
                Err(e) => debug!("Handling of query response returned error {:?}\n", e),
            },
            _ => {}
        }
    }

    async fn ibc_event_handler(&mut self, ev: ChainEvent<O>) -> Result<(), BoxError> {
        match ev.event {
            BuilderEvent::NewBlock => self.new_block_handler(ev)?,
            BuilderEvent::CreateClient | BuilderEvent::UpdateClient => self.client_handler(ev)?,
            BuilderEvent::ConnectionOpenInit => self.handshake_event_handler(&ev).await?,

            _ => {}
        }
        Ok(())
    }

    fn new_block_handler(&mut self, n: ChainEvent<O>) -> Result<(), BoxError> {
        self.relayer_state.new_block_update(n)
    }

    fn client_handler(&mut self, ev: ChainEvent<O>) -> Result<(), BoxError> {
        self.relayer_state.client_handler(ev)
    }

    async fn query_response_handler(
        &mut self,
        r: &ChainQueryResponse<O, Q>,
    ) -> Result<(), BoxError> {

        let requests = self.relayer_state
            .query_response_handler(r.trigger.chain, r.trigger.clone(), r)?;

        self.send_builder_requests(r.trigger.clone(), requests)
            .await?;
        Ok(())
    }

    async fn send_builder_requests(
        &mut self,
        trigger: BuilderTrigger<O>,
        requests: BuilderRequests<O, Q>,
    ) -> Result<(), BoxError> {
        // Send any required queries to Chain or local Light Clients
        for request in requests.src_queries {
            self.query_request_tx
                .send(request)
                .await?;
        }

        for request in requests.dest_queries {
            self.query_request_tx
                .send(request)
                .await?;
        }

        if let Some(request) = requests.src_client_request {
            self.light_client_request_tx
                .send(LightClientQuery {
                    trigger: trigger.clone(),
                    request,
                })
                .await?;
        }

        if let Some(request) = requests.dest_client_request {
            self.light_client_request_tx
                .send(LightClientQuery {
                    trigger: trigger.clone(),
                    request,
                })
                .await?;
        }
        Ok(())
    }

    async fn handshake_event_handler(&mut self, ev: &ChainEvent<O>) -> Result<(), BoxError> {
        // Call the main relayer state handler
        // TODO - check that realyer should relay between the chains and for this connection
        let requests = self.relayer_state.handshake_event_handler(ev)?;

        self.send_builder_requests(
            BuilderTrigger {
                chain: ev.trigger_chain.clone(),
                obj: ev.trigger_object.clone().ok_or("event with no object")?,
            },
            requests,
        )
        .await?;
        Ok(())
    }
}
