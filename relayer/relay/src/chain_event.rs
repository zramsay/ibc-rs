use crate::chain_event_connection::ConnectionBuilderObject;
use crate::relayer_state::BuilderObject;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::query::IbcQuery;
use tendermint::block::Height;

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
pub struct ChainEvent<O>
where
    O: BuilderObject,
{
    pub trigger_chain: ChainId,
    pub chain_height: Height,
    pub event: BuilderEvent,
    pub trigger_object: Option<O>,
}

impl<O> ChainEvent<O>
where
    O: BuilderObject,
{
    pub fn new_from_ibc_event(trigger_chain: ChainId, event: IBCEvent) -> Result<Self, BoxError> {
        match event {
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
                event: BuilderEvent::ConnOpenInit,
                trigger_object: Some(ConnectionBuilderObject::new(&event)),
            }),

            _ => Err("Unrecognized event".into()),
        }
    }

    pub fn src_query<T>(&self, prove: bool) -> Result<dyn IbcQuery<Response = T>, BoxError> {
        Ok(self
            .trigger_object
            .ok_or("not applicable".into())?
            .build_ibc_query(self.chain_height, prove))
    }

    pub fn dest_query<T>(&self, prove: bool) -> Result<dyn IbcQuery<Response = T>, BoxError> {
        Ok(self
            .trigger_object
            .ok_or("not applicable".into())?
            .build_flipped_ibc_query(Height::from(0), prove))
    }
}
