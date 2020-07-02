use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use tendermint::block::Height;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct NewBlockBuilderObject {
    block_height: Height,
}

impl NewBlockBuilderObject {
    pub fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::NewBlock(ev) => Ok(NewBlockBuilderObject {
                block_height: ev.height,
            }),
            _ => Err("not implemented".into()),
        }
    }
}
