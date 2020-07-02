use crate::chain_event_block::NewBlockBuilderObject;
use crate::chain_event_client::ClientBuilderObject;
use crate::chain_event_connection::ConnectionBuilderObject;
use crate::chain_querier::ChainQueryRequest;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics24_host::identifier::ClientId;
use tendermint::block::Height;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub enum BuilderObject {
    NewBlock(NewBlockBuilderObject),
    ClientBuilderObject(ClientBuilderObject),
    ConnectionBuilderObject(ConnectionBuilderObject),
}

impl BuilderObject {
    pub fn flipped(&self) -> Result<Self, BoxError> {
        match self {
            BuilderObject::ConnectionBuilderObject(conn) => {
                Ok(BuilderObject::ConnectionBuilderObject(conn.flipped()))
            }

            _ => Ok(self.clone()), // should this return err?
        }
    }

    pub fn client_id(&self) -> Result<ClientId, BoxError> {
        match self {
            BuilderObject::ClientBuilderObject(cl) => Ok(cl.client_id.clone()),
            BuilderObject::ConnectionBuilderObject(conn) => Ok(conn.client_id.clone()),

            _ => Err("cannot determine client id".into()),
        }
    }

    pub fn client_height(&self) -> Result<Height, BoxError> {
        match self {
            BuilderObject::ClientBuilderObject(cl) => Ok(cl.client_height),

            _ => Err("cannot determin client height".into()),
        }
    }

    pub fn counterparty_client_id(&self) -> Result<ClientId, BoxError> {
        match self {
            BuilderObject::ClientBuilderObject(cl) => Ok(cl.client_id.clone()),
            BuilderObject::ConnectionBuilderObject(conn) => Ok(conn.counterparty_client_id.clone()),

            _ => Err("cannot find client id".into()),
        }
    }
    pub fn new_query_request(&self) -> Result<ChainQueryRequest, BoxError> {
        match self {
            BuilderObject::ConnectionBuilderObject(conn) => Ok(conn.new_query_request()),
            _ => Err("cannot build query".into()),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub enum BuilderEvent {
    NewBlock,
    CreateClient,
    UpdateClient,
    ConnectionOpenInit,
    ConnectionOpenTry,
    ConnectionOpenAck,
    ConnectionOpenConfirm,
    ChannelOpenInit,
    ChannelOpenTry,
    ChannelOpenAck,
    ChannelOpenConfirm,
    // TODO
}

#[derive(Debug, Clone)]
pub struct ChainEvent {
    pub trigger_chain: ChainId,
    pub chain_height: Height,
    pub event: BuilderEvent,
    pub trigger_object: BuilderObject,
}

impl ChainEvent {
    pub fn new_from_ibc_event(trigger_chain: ChainId, event: IBCEvent) -> Result<Self, BoxError> {
        match event.clone() {
            IBCEvent::NewBlock(nb) => Ok(ChainEvent {
                trigger_chain,
                chain_height: nb.height,
                event: BuilderEvent::NewBlock,
                trigger_object: BuilderObject::NewBlock(NewBlockBuilderObject::new(&event)?),
            }),
            IBCEvent::CreateClient(cc) => Ok(ChainEvent {
                trigger_chain,
                chain_height: cc.height,
                event: BuilderEvent::CreateClient,
                trigger_object: BuilderObject::ClientBuilderObject(ClientBuilderObject::new(
                    &event,
                )?),
            }),
            IBCEvent::UpdateClient(uc) => Ok(ChainEvent {
                trigger_chain,
                chain_height: uc.height,
                event: BuilderEvent::UpdateClient,
                trigger_object: BuilderObject::ClientBuilderObject(ClientBuilderObject::new(
                    &event,
                )?),
            }),
            IBCEvent::OpenInitConnection(conn) => Ok(ChainEvent {
                trigger_chain,
                chain_height: conn.height,
                event: BuilderEvent::ConnectionOpenInit,
                trigger_object: BuilderObject::ConnectionBuilderObject(
                    ConnectionBuilderObject::new(&event)?,
                ),
            }),

            _ => Err("Unrecognized event".into()),
        }
    }
}

pub(crate) fn requires_updated_b_client_on_a(event: BuilderEvent) -> bool {
    match event {
        BuilderEvent::ConnectionOpenInit | BuilderEvent::ConnectionOpenTry => true,
        _ => false,
    }
}

pub(crate) fn requires_consensus_proof_for_b_client_on_a(event: BuilderEvent) -> bool {
    match event {
        BuilderEvent::ConnectionOpenInit | BuilderEvent::ConnectionOpenTry => true,
        _ => false,
    }
}
