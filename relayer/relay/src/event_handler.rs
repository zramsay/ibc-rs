use relayer_modules::events::IBCEvent;
use tokio::sync::mpsc::{Receiver, Sender};

use crate::chain_querier::{ChainQuerierResponse, ChainQuery};
use crate::config::Config;
use crate::light_client_querier::{LightClientQuerierResponse, LightClientQuery};
use crate::relayer_state::{BuilderRequests, RelayerState};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics02_client::events as ClientEvents;
use relayer_modules::ics02_client::events::NewBlock;
use relayer_modules::ics02_client::state::ConsensusState;
use relayer_modules::ics03_connection::exported::State;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};
use tendermint::block;
use tracing::{debug, info};

pub enum RelayerEvent<CS>
where
    CS: ConsensusState,
{
    ChainEvent(ChainEvent),
    QueryEvent(ChainQuerierResponse<CS>),
    LightClientEvent(LightClientQuerierResponse),
}

#[derive(Debug, Clone)]
pub struct ChainEvent {
    from_chain: ChainId,
    event: IBCEvent,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConnectionEventObject {
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty_connection_id: ConnectionId,
    pub counterparty_client_id: ClientId,
}

impl ConnectionEventObject {
    pub fn flipped(self) -> ConnectionEventObject {
        ConnectionEventObject {
            connection_id: self.counterparty_connection_id,
            client_id: self.counterparty_client_id,
            counterparty_connection_id: self.connection_id,
            counterparty_client_id: self.client_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BuilderTrigger {
    pub trigger_chain: ChainId,
    pub trigger_object: BuilderObject,
}

impl BuilderTrigger {
    pub fn get_trigger_client_id(self) -> Result<ClientId, BoxError> {
        match self.trigger_object {
            BuilderObject::ConnectionEvent(conn) => Ok(conn.client_id),
        }
    }

    pub fn get_trigger_counterparty_client_id(self) -> Result<ClientId, BoxError> {
        match self.trigger_object {
            BuilderObject::ConnectionEvent(conn) => Ok(conn.counterparty_client_id),
        }
    }

    pub fn get_trigger_connection_id(self) -> Result<ConnectionId, BoxError> {
        match self.trigger_object {
            BuilderObject::ConnectionEvent(conn) => Ok(conn.connection_id),
        }
    }

    pub fn get_trigger_counterparty_connection_id(self) -> Result<ConnectionId, BoxError> {
        match self.trigger_object {
            BuilderObject::ConnectionEvent(conn) => Ok(conn.connection_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuilderObject {
    ConnectionEvent(ConnectionEventObject),
}

/// The Event Handler handles IBC events from the monitors.
pub struct EventHandler<CS>
where
    CS: ConsensusState,
{
    /// If true the handler processes event and attempts to relay,
    /// otherwise it only dumps the events.
    relay: bool,
    config: Config,

    /// Channel where events from the different chains are received
    chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,

    /// Channel where query requests are sent
    /// TODO - make one querier per chain
    query_request_tx: Sender<ChainQuery>,
    /// Channel where query responses are received
    query_response_rx: Receiver<ChainQuerierResponse<CS>>,

    light_client_request_tx: Sender<LightClientQuery>,
    light_client_response_rx: Receiver<LightClientQuerierResponse>,

    /// Relayer state, updated by the different events on _rx channels
    relayer_state: RelayerState<CS>,
}

impl<CS> EventHandler<CS>
where
    CS: ConsensusState,
{
    /// Constructor for the Event Handler
    pub fn new(
        relay: bool,
        config: &Config,
        chain_ev_rx: Receiver<(ChainId, Vec<IBCEvent>)>,
        query_request_tx: Sender<ChainQuery>,
        query_response_rx: Receiver<ChainQuerierResponse<CS>>,
        light_client_request_tx: Sender<LightClientQuery>,
        light_client_response_rx: Receiver<LightClientQuerierResponse>,
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
                    let _handle = self.event_handler(RelayerEvent::ChainEvent(ChainEvent {
                        from_chain: events.0,
                        event,
                    }));
                }
            }
            if let Some(event) = self.query_response_rx.recv().await {
                let _handle = self.event_handler(RelayerEvent::QueryEvent(event));
            }
        }
    }

    async fn event_handler(&mut self, event: RelayerEvent<CS>)
    where
        CS: ConsensusState,
    {
        match event {
            RelayerEvent::ChainEvent(ibc_ev) => match self.ibc_event_handler(ibc_ev).await {
                Ok(()) => debug!("Successful handling of event\n"),
                Err(e) => debug!("Handling of event returned {}\n", e),
            },
            RelayerEvent::QueryEvent(response) => match self.query_response_handler(response).await
            {
                Ok(()) => debug!("Successful handling of query response\n"),
                Err(e) => debug!("Handling of query response returned error {:?}\n", e),
            },
            _ => {}
        }
    }

    fn new_block_handler(&mut self, from: ChainId, nb: NewBlock) -> Result<(), BoxError> {
        self.relayer_state.new_block_update(from, nb)
    }

    fn create_client_handler(
        &mut self,
        from: ChainId,
        cc: ClientEvents::CreateClient,
    ) -> Result<(), BoxError> {
        self.relayer_state.create_client_handler(from, cc)
    }

    fn update_client_handler(
        &mut self,
        from: ChainId,
        uc: ClientEvents::UpdateClient,
    ) -> Result<(), BoxError> {
        self.relayer_state.update_client_handler(from, uc)
    }

    async fn query_response_handler(
        &mut self,
        r: ChainQuerierResponse<CS>,
    ) -> Result<(), BoxError> {
        // TODO - check that realyer should relay between the chains and for this connection

        self.relayer_state
            .query_response_handler(r.from_chain, r.trigger.clone(), r.response)?;

        let requests = self
            .relayer_state
            .message_builder_next_step(r.trigger.clone())?;

        self.send_builder_requests(r.trigger.clone(), requests)
            .await?;
        Ok(())
    }

    async fn send_builder_requests(
        &mut self,
        trigger: BuilderTrigger,
        requests: BuilderRequests,
    ) -> Result<(), BoxError> {
        for request in requests.src_queries {
            self.query_request_tx
                .send(ChainQuery {
                    trigger: trigger.clone(),
                    request,
                })
                .await?;
        }

        // Send any required queries to Chain or local Light Clients
        for request in requests.dest_queries {
            self.query_request_tx
                .send(ChainQuery {
                    trigger: trigger.clone(),
                    request,
                })
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

    async fn connection_handler(
        &mut self,
        from_chain: ChainId,
        height: block::Height,
        state: State,
        conn: ConnectionEventObject,
    ) -> Result<(), BoxError> {
        // Call the main relayer state handler
        // TODO - check that realyer should relay between the chains and for this connection
        let requests =
            self.relayer_state
                .connection_handler(from_chain, height, state, conn.clone())?;

        self.send_builder_requests(
            BuilderTrigger {
                trigger_chain: from_chain,
                trigger_object: BuilderObject::ConnectionEvent(conn.clone()),
            },
            requests,
        )
        .await?;
        Ok(())
    }

    async fn ibc_event_handler(&mut self, n: ChainEvent) -> Result<(), BoxError> {
        match n.event {
            IBCEvent::NewBlock(nb) => self.new_block_handler(n.from_chain, nb)?,
            IBCEvent::CreateClient(cc) => self.create_client_handler(n.from_chain, cc)?,
            IBCEvent::UpdateClient(uc) => self.update_client_handler(n.from_chain, uc)?,
            IBCEvent::OpenInitConnection(oi) => {
                self.connection_handler(
                    n.from_chain,
                    oi.height,
                    State::Init,
                    ConnectionEventObject {
                        connection_id: oi.connection_id,
                        client_id: oi.client_id.clone(),
                        counterparty_connection_id: oi.counterparty_connection_id,
                        counterparty_client_id: oi.client_id.clone(),
                    },
                )
                .await?
            }

            _ => {}
        }
        Ok(())
    }
}
