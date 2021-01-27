use crate::ics02_client::state::ClientState;
use crate::ics02_client::{client_def::AnyClient, client_def::ClientDef};
use crate::ics03_connection::connection::ConnectionEnd;
use crate::ics04_channel::channel::ChannelEnd;
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::{Error, Kind};
use crate::ics05_port::capabilities::Capability;
use crate::ics24_host::identifier::{ConnectionId, PortId};
use crate::proofs::Proofs;

pub(crate) fn verify_connection_and_capability(
    ctx: &dyn ChannelReader,
    channel_end: &ChannelEnd,
    port_id: &PortId,
) -> Result<(ConnectionId, ConnectionEnd, Capability), Error> {
    if channel_end.connection_hops().len() != 1 {
        return Err(Kind::InvalidConnectionHopsLength.into());
    }

    // An IBC connection running on the local (host) chain should exist.
    let connection_id = channel_end.connection_hops()[0].clone();
    let connection_end = ctx
        .connection_end(&connection_id)
        .ok_or_else(|| Kind::MissingConnection(connection_id.clone()))?;

    // Check that a single version has been negotiated.
    let version = match connection_end.versions().as_slice() {
        [version] => version,
        _ => return Err(Kind::InvalidVersionLengthConnection.into()),
    };

    // Check that the version negotiated supports the channel's ordering
    let channel_feature = channel_end.ordering().as_string().to_string();
    if !version.is_supported_feature(&channel_feature) {
        return Err(Kind::ChannelFeatureNotSuportedByConnection.into());
    }

    // TODO: Check that `version` is non empty but not necessary coherent
    if channel_end.version().is_empty() {
        return Err(Kind::InvalidVersion.into());
    }

    let channel_cap = match ctx.port_capability(port_id) {
        Some(channel_cap) => {
            if !ctx.capability_authentification(port_id, &channel_cap) {
                return Err(Kind::InvalidPortCapability.into());
            } else {
                channel_cap
            }
        }
        None => return Err(Kind::NoPortCapability.into()),
    };

    Ok((connection_id, connection_end, channel_cap))
}

/// Entry point for verifying all proofs bundled in any ICS4 message.
pub fn verify_proofs(
    ctx: &dyn ChannelReader,
    channel_end: &ChannelEnd,
    expected_channel_end: &ChannelEnd,
    proofs: &Proofs,
) -> Result<(), Error> {
    let connection_id = &channel_end.connection_hops()[0];
    let connection_end = ctx
        .connection_end(connection_id)
        .ok_or_else(|| Kind::MissingConnection(connection_id.clone()))?;

    let port_channel_id = (
        channel_end.counterparty().port_id().clone(),
        channel_end.counterparty().channel_id().clone().unwrap(),
    );

    let client_state = ctx
        .channel_client_state(&port_channel_id)
        .ok_or(Kind::MissingClientState)?;

    // // Fetch the client state (IBC client on the local/host chain).
    // let client_state = ctx.channel_client_state(&(port_id.clone(), chan_id.clone()));

    //let client_st = client_state.ok_or(Kind::MissingClientState)?;

    let client_id = connection_end.client_id();

    // The client must not be frozen.
    if client_state.is_frozen() {
        return Err(Kind::FrozenClient.context(client_id.to_string()).into());
    }

    if ctx
        .channel_client_consensus_state(&port_channel_id, proofs.height())
        .is_none()
    {
        return Err(Kind::MissingClientConsensusState
            .context(client_id.to_string())
            .into());
    }

    let client_def = AnyClient::from_client_type(client_state.client_type());

    // Verify the proof for the channel state against the expected channel end.
    // A counterparty channel id of None in not possible, and is checked by validate_basic in msg.
    client_def
        .verify_channel_state(
            &client_state,
            proofs.height(),
            connection_end.counterparty().prefix(),
            proofs.object_proof(),
            channel_end.counterparty().port_id(),
            channel_end.counterparty().channel_id().as_ref().unwrap(),
            expected_channel_end,
        )
        .map_err(|_| Kind::InvalidProof.into())
}
