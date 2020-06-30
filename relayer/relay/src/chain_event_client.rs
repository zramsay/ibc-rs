use crate::relayer_state::BuilderObject;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics02_client::client_type::ClientType;
use relayer_modules::ics24_host::identifier::ClientId;
use tendermint::block::Height;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct ClientBuilderObject {
    height: Height,
    client_id: ClientId,
    client_type: ClientType,
    client_height: Height,
}

impl ClientBuilderObject {
    pub fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::CreateClient(cl) => Ok(ClientBuilderObject {
                height: cl.height,
                client_id: cl.clone().client_id,
                client_type: cl.clone().client_type,
                client_height: cl.client_height,
            }),
            IBCEvent::UpdateClient(cl) => Ok(ClientBuilderObject {
                height: cl.height,
                client_id: cl.clone().client_id,
                client_type: cl.clone().client_type,
                client_height: cl.client_height,
            }),
            _ => Err("not implemented".into()),
        }
    }
}

impl BuilderObject for ClientBuilderObject {
    fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::CreateClient(cl) => Ok(ClientBuilderObject {
                height: cl.height,
                client_id: cl.clone().client_id,
                client_type: cl.clone().client_type,
                client_height: cl.client_height,
            }),
            IBCEvent::UpdateClient(cl) => Ok(ClientBuilderObject {
                height: cl.height,
                client_id: cl.clone().client_id,
                client_type: cl.clone().client_type,
                client_height: cl.client_height,
            }),
            _ => Err("not implemented".into()),
        }
    }

    fn flipped(&self) -> Option<Self> {
        unimplemented!()
    }

    fn client_id(&self) -> ClientId {
        self.client_id.clone()
    }

    fn client_height(&self) -> Height {
        self.client_height
    }

    fn counterparty_client_id(&self) -> ClientId {
        unimplemented!()
    }
}
