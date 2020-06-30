use crate::relayer_state::BuilderObject;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use tendermint::block::Height;

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
    pub trigger_object: Option<Box<dyn BuilderObject>>,
}

impl ChainEvent {
    pub fn new_from_ibc_event(trigger_chain: ChainId, event: IBCEvent) -> Result<Self, BoxError> {
        match event.clone() {
            IBCEvent::NewBlock(nb) => Ok(ChainEvent {
                trigger_chain,
                chain_height: nb.height,
                event: BuilderEvent::NewBlock,
                trigger_object: None,
            }),
            IBCEvent::CreateClient(cc) => Ok(ChainEvent {
                trigger_chain,
                chain_height: cc.height,
                event: BuilderEvent::CreateClient,
                trigger_object: None,
            }),
            IBCEvent::UpdateClient(uc) => Ok(ChainEvent {
                trigger_chain,
                chain_height: uc.height,
                event: BuilderEvent::UpdateClient,
                trigger_object: None,
            }),
            IBCEvent::OpenInitConnection(conn) => Ok(ChainEvent {
                trigger_chain,
                chain_height: conn.height,
                event: BuilderEvent::ConnectionOpenInit,
                trigger_object: Some(BuilderObject::new(&event.clone())?),
            }),

            _ => Err("Unrecognized event".into()),
        }
    }
}
