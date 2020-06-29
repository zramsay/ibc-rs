use crate::relayer_state::BuilderObject;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics02_client::client_type::ClientType;
use relayer_modules::ics02_client::query::QueryClientFullState;
use relayer_modules::ics24_host::identifier::ClientId;
use relayer_modules::query::IbcQuery;
use tendermint::block::Height;

pub struct ClientBuilderObject {
    height: Height,
    client_id: ClientId,
    client_type: ClientType,
    client_height: Height,
}

impl ClientBuilderObject {
    pub fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::CreateClient(cl) | IBCEvent::UpdateClient(cl) => Ok(ClientBuilderObject {
                height: *cl.height,
                client_id: *cl.client_id,
                client_type: *cl.client_type,
                client_height: *cl.client_height,
            }),
            _ => Err("not implemented".into()),
        }
    }
}

impl BuilderObject for ClientBuilderObject {
    fn flipped(&self) -> Option<Self> {
        unimplemented!()
    }

    fn client_id(&self) -> ClientId {
        *self.client_id
    }

    fn client_height(&self) -> Height {
        *self.client_height
    }

    fn counterparty_client_id(&self) -> ClientId {
        unimplemented!()
    }

    fn build_ibc_query<T>(&self, height: Height, prove: bool) -> &dyn IbcQuery<Response = T> {
        &QueryClientFullState::new(u64::from(height), self.client_id, prove)
    }

    fn build_flipped_ibc_query<T>(
        &self,
        height: Height,
        prove: bool,
    ) -> &dyn IbcQuery<Response = T> {
        unimplemented!()
    }
}
