use crate::chain_querier::{ChainQueryRequest, ConnectionParams};
use anomaly::BoxError;
use relayer_modules::events::IBCEvent;
use relayer_modules::ics24_host::identifier::{ClientId, ConnectionId};

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct ConnectionBuilderObject {
    pub connection_id: ConnectionId,
    pub client_id: ClientId,
    pub counterparty_connection_id: ConnectionId,
    pub counterparty_client_id: ClientId,
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
    pub fn flipped(&self) -> Self {
        ConnectionBuilderObject {
            connection_id: self.counterparty_connection_id.clone(),
            client_id: self.counterparty_client_id.clone(),
            counterparty_connection_id: self.connection_id.clone(),
            counterparty_client_id: self.client_id.clone(),
        }
    }
    pub fn new_query_request(&self) -> ChainQueryRequest {
        ChainQueryRequest::ConnectionParams(ConnectionParams {
            connection_id: self.connection_id.clone(),
        })
    }
}
