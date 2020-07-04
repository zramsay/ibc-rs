use relayer_modules::events::IBCEvent;
use tokio::sync::mpsc::{Receiver, Sender};

use crate::chain_event::{BuilderEvent, ChainEvent};
use crate::chain_querier::{ChainQueryRequestParams, ChainQueryResponse};
use crate::config::Config;
use crate::light_client_querier::{LightClientQuery, LightClientQueryResponse};
use crate::message_builder::BuilderRequests;
use crate::relayer_state::RelayerState;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use tracing::{debug, info};

#[derive(Debug, Clone)]
pub enum RelayerEvent {
    ChainEvent(ChainEvent),
    QueryEvent(ChainQueryResponse),
    LightClientEvent(LightClientQueryResponse),
}

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler {
    /// If true the handler processes event and attempts to relay,
    /// otherwise it only dumps the events.
    relay: bool,
    //config: Config,
    /// Channel where events from the different chains are received
    chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,

    /// Channel where query requests are sent
    /// TODO - make one querier per chain
    query_request_tx: Sender<ChainQueryRequestParams>,
    /// Channel where query responses are received
    query_response_rx: Receiver<ChainQueryResponse>,

    light_client_request_tx: Sender<LightClientQuery>,
    light_client_response_rx: Receiver<LightClientQueryResponse>,

    /// Relayer state, updated by the different events on _rx channels
    relayer_state: RelayerState,
}

impl EventHandler {
    /// Constructor for the Event Handler
    pub fn new(
        relay: bool,
        config: &Config,
        chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,
        query_request_tx: Sender<ChainQueryRequestParams>,
        query_response_rx: Receiver<ChainQueryResponse>,
        light_client_request_tx: Sender<LightClientQuery>,
        light_client_response_rx: Receiver<LightClientQueryResponse>,
    ) -> Self {
        EventHandler {
            relay,
            //config: config.clone(),
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
                    if let Ok(ev) = ChainEvent::new_from_ibc_event(events.0, event) {
                        let _handle = self.event_handler(RelayerEvent::ChainEvent(ev)).await;
                    }
                }
            }

            // TODO Move to crossbeam so we can select?
            // if let Some(event) = self.query_response_rx.recv().await {
            //     let _handle = self.event_handler(RelayerEvent::QueryEvent(event));
            // }
        }
    }

    async fn event_handler(&mut self, event: RelayerEvent) {
        match event {
            RelayerEvent::ChainEvent(chain_event) => {
                match self.ibc_event_handler(chain_event).await {
                    Ok(()) => debug!("Successful handling of chain event\n"),
                    Err(e) => debug!("Handling of event returned {}\n", e),
                }
            }
            RelayerEvent::QueryEvent(response) => {
                match self.query_response_handler(&response).await {
                    Ok(()) => debug!("Successful handling of query response\n"),
                    Err(e) => debug!("Handling of query response returned error {:?}\n", e),
                }
            }
            _ => {}
        }
    }

    async fn ibc_event_handler(&mut self, ev: ChainEvent) -> Result<(), BoxError> {
        match ev.event {
            BuilderEvent::NewBlock => self.new_block_handler(ev).await?,
            BuilderEvent::CreateClient | BuilderEvent::UpdateClient => self.client_handler(ev)?,
            _ => self.handshake_event_handler(&ev).await?,
        }
        Ok(())
    }

    async fn new_block_handler(&mut self, n: ChainEvent) -> Result<(), BoxError> {
        let requests = self.relayer_state.new_block_update(n)?;
        self.send_builder_requests(requests).await?;
        Ok(())
    }

    fn client_handler(&mut self, ev: ChainEvent) -> Result<(), BoxError> {
        self.relayer_state.client_handler(ev)
    }

    async fn query_response_handler(&mut self, r: &ChainQueryResponse) -> Result<(), BoxError> {
        let requests = self.relayer_state.query_response_handler(r)?;
        self.send_builder_requests(requests).await?;
        Ok(())
    }

    async fn send_builder_requests(&mut self, requests: BuilderRequests) -> Result<(), BoxError> {
        // Send any required queries to Chain or local Light Clients
        for request in requests.src_queries {
            self.query_request_tx.send(request).await?;
        }

        for request in requests.dest_queries {
            self.query_request_tx.send(request).await?;
        }

        if let Some(request) = requests.src_client_request {
            self.light_client_request_tx.send(request).await?;
        }

        if let Some(request) = requests.dest_client_request {
            self.light_client_request_tx.send(request).await?;
        }
        Ok(())
    }

    async fn handshake_event_handler(&mut self, ev: &ChainEvent) -> Result<(), BoxError> {
        // Call the main relayer state handler
        // TODO - check that realyer should relay between the chains and for this connection
        let requests = self.relayer_state.handshake_event_handler(ev)?;

        self.send_builder_requests(requests).await?;
        Ok(())
    }
}
