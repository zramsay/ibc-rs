use crate::ics02_client::events as ClientEvents;
use crate::ics03_connection::events as ConnectionEvents;
use crate::ics04_channel::events as ChannelEvents;
use crate::ics20_fungible_token_transfer::events as TransferEvents;
use serde_derive::{Deserialize, Serialize};
use std::convert::TryFrom;
use tendermint::rpc::event_listener::ResultEvent;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum IBCEvent {
    CreateClient(ClientEvents::CreateClient),
    UpdateClient(ClientEvents::UpdateClient),
    ClientMisbehavior(ClientEvents::ClientMisbehavior),
    OpenInitConnection(ConnectionEvents::OpenInit),
    OpenTryConnection(ConnectionEvents::OpenTry),
    OpenAckConnection(ConnectionEvents::OpenAck),
    OpenConfirmConnection(ConnectionEvents::OpenConfirm),
    SendPacketChannel(ChannelEvents::SendPacket),
    RecievePacketChannel(ChannelEvents::RecievePacket),
    AcknowledgePacketChannel(ChannelEvents::AcknowledgePacket),
    CleanupPacketChannel(ChannelEvents::CleanupPacket),
    TimeoutPacketChannel(ChannelEvents::TimeoutPacket),
    OpaquePacket(ChannelEvents::OpaquePacket),
    TimeoutTransferEvent(TransferEvents::Timeout),
    PacketTransfer(TransferEvents::Packet),
    ChannelClosedTranfer(TransferEvents::ChannelClosed),
}



impl IBCEvent {
    pub fn get_all_events(event: ResultEvent) -> Vec<IBCEvent> {
        let mut vals: Vec<IBCEvent> = vec![];
        if let Ok(ev) = ClientEvents::CreateClient::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ClientEvents::UpdateClient::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ClientEvents::ClientMisbehavior::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenInit::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenTry::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenAck::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ConnectionEvents::OpenConfirm::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::SendPacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::RecievePacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::AcknowledgePacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::CleanupPacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::TimeoutPacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = ChannelEvents::OpaquePacket::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = TransferEvents::Timeout::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = TransferEvents::Packet::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        if let Ok(ev) = TransferEvents::ChannelClosed::try_from(&event) {
            vals.push(IBCEvent::from(ev));
        }
        return vals;
    }
}
impl From<ChannelEvents::OpaquePacket> for IBCEvent {
    fn from(v: ChannelEvents::OpaquePacket) -> Self {
        IBCEvent::OpaquePacket(v)
    }
}

impl From<TransferEvents::Timeout> for IBCEvent {
    fn from(v: TransferEvents::Timeout) -> Self {
        IBCEvent::TimeoutTransferEvent(v)
    }
}

impl From<ChannelEvents::TimeoutPacket> for IBCEvent {
    fn from(v: ChannelEvents::TimeoutPacket) -> Self {
        IBCEvent::TimeoutPacketChannel(v)
    }
}

impl From<ChannelEvents::CleanupPacket> for IBCEvent {
    fn from(v: ChannelEvents::CleanupPacket) -> Self {
        IBCEvent::CleanupPacketChannel(v)
    }
}

impl From<ChannelEvents::AcknowledgePacket> for IBCEvent {
    fn from(v: ChannelEvents::AcknowledgePacket) -> Self {
        IBCEvent::AcknowledgePacketChannel(v)
    }
}

impl From<ChannelEvents::RecievePacket> for IBCEvent {
    fn from(v: ChannelEvents::RecievePacket) -> Self {
        IBCEvent::RecievePacketChannel(v)
    }
}

impl From<ChannelEvents::SendPacket> for IBCEvent {
    fn from(v: ChannelEvents::SendPacket) -> Self {
        IBCEvent::SendPacketChannel(v)
    }
}

impl From<ConnectionEvents::OpenConfirm> for IBCEvent {
    fn from(v: ConnectionEvents::OpenConfirm) -> Self {
        IBCEvent::OpenConfirmConnection(v)
    }
}

impl From<ConnectionEvents::OpenAck> for IBCEvent {
    fn from(v: ConnectionEvents::OpenAck) -> Self {
        IBCEvent::OpenAckConnection(v)
    }
}

impl From<ConnectionEvents::OpenTry> for IBCEvent {
    fn from(v: ConnectionEvents::OpenTry) -> Self {
        IBCEvent::OpenTryConnection(v)
    }
}

impl From<ConnectionEvents::OpenInit> for IBCEvent {
    fn from(v: ConnectionEvents::OpenInit) -> Self {
        IBCEvent::OpenInitConnection(v)
    }
}

impl From<ClientEvents::ClientMisbehavior> for IBCEvent {
    fn from(v: ClientEvents::ClientMisbehavior) -> Self {
        IBCEvent::ClientMisbehavior(v)
    }
}

impl From<ClientEvents::UpdateClient> for IBCEvent {
    fn from(v: ClientEvents::UpdateClient) -> Self {
        IBCEvent::UpdateClient(v)
    }
}

impl From<ClientEvents::CreateClient> for IBCEvent {
    fn from(v: ClientEvents::CreateClient) -> Self {
        IBCEvent::CreateClient(v)
    }
}

impl From<TransferEvents::ChannelClosed> for IBCEvent {
    fn from(v: TransferEvents::ChannelClosed) -> Self {
        IBCEvent::ChannelClosedTranfer(v)
    }
}

impl From<TransferEvents::Packet> for IBCEvent {
    fn from(v: TransferEvents::Packet) -> Self {
        IBCEvent::PacketTransfer(v)
    }
}

pub fn extract_events(result: &ResultEvent, action_string: &str)->Result<std::collections::HashMap<String,Vec<String>>,Box<dyn std::error::Error>>{
    if let Some(ref events) = result.events {
    if let Some(message_action) = events.get("message.action") {
        if message_action.contains(&action_string.to_owned()) {
            return Ok(events.clone());
        }
}
    }
    Err("Incorrect Event Type".into())
}
#[macro_export]
macro_rules! make_event {
    ($a:ident, $b:literal) => {
        #[derive(Debug, Deserialize, Serialize, Clone)]
        pub struct $a {
            pub data: std::collections::HashMap<String, Vec<String>>,
        }
        impl TryFrom<&ResultEvent> for $a {
            type Error = Box<dyn std::error::Error>;
            fn try_from(result: &ResultEvent) -> Result<Self, Self::Error> {
                Ok($a {data:crate::events::extract_events(result,$b)?.clone()})
            }
        }
    };
}
