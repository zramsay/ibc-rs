use crate::relayer_state::BuilderObject;
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics03_connection::query::QueryConnection;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};
use relayer_modules::query::IbcQuery;
use tendermint::block::Height;

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
                connection_id: *conn.connection_id,
                client_id: *conn.client_id,
                counterparty_connection_id: *conn.counterparty_connection_id,
                counterparty_client_id: *conn.counterparty_client_id,
            }),
            _ => Err("not implemented".into()),
        }
    }
}

impl BuilderObject for ConnectionBuilderObject {
    fn flipped(self) -> Option<Self> {
        Some(ConnectionBuilderObject {
            connection_id: self.counterparty_connection_id,
            client_id: self.counterparty_client_id,
            counterparty_connection_id: self.connection_id,
            counterparty_client_id: self.client_id,
        })
    }

    fn client_id(&self) -> ClientId {
        *self.client_id
    }

    fn client_height(&self) -> Height {
        unimplemented!()
    }

    fn counterparty_client_id(&self) -> ClientId {
        *self.counterparty_client_id
    }

    fn build_ibc_query<T>(&self, height: Height, prove: bool) -> &dyn IbcQuery<Response = T> {
        &QueryConnection::new(u64::from(height), self.connection_id, prove)
    }

    fn build_flipped_ibc_query<T>(
        &self,
        height: Height,
        prove: bool,
    ) -> &dyn IbcQuery<Response = T> {
        &QueryConnection::new(u64::from(height), self.counterparty_connection_id, prove)
    }
}
