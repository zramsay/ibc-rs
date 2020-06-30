use crate::relayer_state::BuilderObject;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};
use tendermint::block::Height;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct ConnectionBuilderObject {
    connection_id: ConnectionId,
    client_id: ClientId,
    counterparty_connection_id: ConnectionId,
    counterparty_client_id: ClientId,
}

impl ConnectionBuilderObject {
    pub fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::OpenInitConnection(conn) => Ok(ConnectionBuilderObject {
                connection_id: conn.connection_id.clone(),
                client_id: conn.client_id.clone(),
                counterparty_connection_id: conn.counterparty_connection_id.clone(),
                counterparty_client_id: conn.counterparty_client_id.clone(),
            }),
            _ => Err("not implemented".into()),
        }
    }
}

impl BuilderObject for ConnectionBuilderObject {
    fn new(ev: &IBCEvent) -> Result<Self, BoxError> {
        match ev {
            IBCEvent::OpenInitConnection(conn) => Ok(ConnectionBuilderObject {
                connection_id: conn.connection_id.clone(),
                client_id: conn.client_id.clone(),
                counterparty_connection_id: conn.counterparty_connection_id.clone(),
                counterparty_client_id: conn.counterparty_client_id.clone(),
            }),
            _ => Err("not implemented".into()),
        }
    }

    fn flipped(&self) -> Option<Self> {
        Some(ConnectionBuilderObject {
            connection_id: self.counterparty_connection_id.clone(),
            client_id: self.counterparty_client_id.clone(),
            counterparty_connection_id: self.connection_id.clone(),
            counterparty_client_id: self.client_id.clone(),
        })
    }

    fn client_id(&self) -> ClientId {
        self.client_id.clone()
    }

    fn client_height(&self) -> Height {
        unimplemented!()
    }

    fn counterparty_client_id(&self) -> ClientId {
        self.counterparty_client_id.clone()
    }

//    fn build_ibc_query<QueryConnection>(&self, height: Height, prove: bool) -> QueryConnection {
//        QueryConnection::new(u64::from(height), self.connection_id.clone(), prove)
//    }
//
//    fn build_flipped_ibc_query<QueryConnection>(
//        &self,
//        height: Height,
//        prove: bool,
//    ) -> QueryConnection {
//        QueryConnection::new(u64::from(height), self.counterparty_connection_id.clone(), prove)
//    }
}
