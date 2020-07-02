use crate::chain_querier::{ChainQueryRequest, ClientConsensusParams};
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics02_client::client_type::ClientType;
use relayer_modules::ics24_host::identifier::ClientId;
use tendermint::block::Height;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct ClientBuilderObject {
    pub height: Height,
    pub client_id: ClientId,
    client_type: ClientType,
    pub client_height: Height,
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

    pub fn consensus_query_request(&self, height: Height) -> ChainQueryRequest {
        ChainQueryRequest::ClientConsensusParams(ClientConsensusParams {
            client_id: self.client_id.clone(),
            consensus_height: height,
        })
    }
}
