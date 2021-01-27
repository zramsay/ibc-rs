//! Protocol logic specific to ICS4 messages of type `MsgChannelOpenInit`.

use crate::events::IBCEvent;
use crate::handler::{HandlerOutput, HandlerResult};
use crate::ics04_channel::channel::{ChannelEnd, State};
use crate::ics04_channel::context::ChannelReader;
use crate::ics04_channel::error::Error;
use crate::ics04_channel::events::Attributes;
use crate::ics04_channel::handler::{verify, ChannelResult};
use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;

pub(crate) fn process(
    ctx: &dyn ChannelReader,
    msg: MsgChannelOpenInit,
) -> HandlerResult<ChannelResult, Error> {
    let mut output = HandlerOutput::builder();

    let port_id = msg.port_id.clone();
    let (_, _, channel_cap) =
        verify::verify_connection_and_capability(ctx, &msg.channel, &port_id)?;

    // TODO: can we just clone `msg.channel()` (after checking that its state is `State::Init`)?
    let channel_end = ChannelEnd::new(
        State::Init,
        msg.channel.ordering(),
        msg.channel.counterparty().clone(),
        msg.channel.connection_hops().clone(),
        msg.channel.version().clone(),
    );

    output.log("success: no channel found");

    let result = ChannelResult {
        port_id,
        channel_id: None,
        channel_cap,
        channel_end,
    };

    let event_attributes = Attributes {
        channel_id: None,
        ..Default::default()
    };
    output.emit(IBCEvent::OpenInitChannel(event_attributes.into()));

    Ok(output.with_result(result))
}

#[cfg(test)]
mod tests {
    use std::convert::TryFrom;
    use std::str::FromStr;

    use crate::events::IBCEvent;
    use crate::ics03_connection::connection::ConnectionEnd;
    use crate::ics03_connection::connection::State as ConnectionState;
    use crate::ics03_connection::msgs::conn_open_init::test_util::get_dummy_msg_conn_open_init;
    use crate::ics03_connection::msgs::conn_open_init::MsgConnectionOpenInit;
    use crate::ics03_connection::version::get_compatible_versions;
    use crate::ics04_channel::channel::State;
    use crate::ics04_channel::handler::{dispatch, ChannelResult};
    use crate::ics04_channel::msgs::chan_open_init::test_util::get_dummy_raw_msg_chan_open_init;
    use crate::ics04_channel::msgs::chan_open_init::MsgChannelOpenInit;
    use crate::ics04_channel::msgs::ChannelMsg;
    use crate::ics24_host::identifier::ConnectionId;
    use crate::mock::context::MockContext;

    #[test]
    fn chan_open_init_msg_processing() {
        struct Test {
            name: String,
            ctx: MockContext,
            msg: ChannelMsg,
            want_pass: bool,
        }

        let msg_chan_init =
            MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init()).unwrap();

        let context = MockContext::default();

        let msg_conn_init =
            MsgConnectionOpenInit::try_from(get_dummy_msg_conn_open_init()).unwrap();

        let init_conn_end = ConnectionEnd::new(
            ConnectionState::Init,
            msg_conn_init.client_id.clone(),
            msg_conn_init.counterparty.clone(),
            get_compatible_versions(),
            msg_conn_init.delay_period,
        );

        let ccid = <ConnectionId as FromStr>::from_str("defaultConnection-0");
        let cid = match ccid {
            Ok(v) => v,
            Err(_e) => ConnectionId::default(),
        };

        let tests: Vec<Test> = vec![
            Test {
                name: "Processing fails because no connection exists in the context".to_string(),
                ctx: context.clone(),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Processing fails because port does not have a capability associated"
                    .to_string(),
                ctx: context
                    .clone()
                    .with_connection(cid.clone(), init_conn_end.clone()),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init.clone()),
                want_pass: false,
            },
            Test {
                name: "Good parameters".to_string(),
                ctx: context
                    .with_connection(cid, init_conn_end)
                    .with_port_capability(
                        MsgChannelOpenInit::try_from(get_dummy_raw_msg_chan_open_init())
                            .unwrap()
                            .port_id
                            .clone(),
                    ),
                msg: ChannelMsg::ChannelOpenInit(msg_chan_init),
                want_pass: true,
            },
        ]
        .into_iter()
        .collect();

        for test in tests {
            let res = dispatch(&test.ctx, test.msg.clone());
            // Additionally check the events and the output objects in the result.
            match res {
                Ok(proto_output) => {
                    assert_eq!(
                        test.want_pass,
                        true,
                        "chan_open_init: test passed but was supposed to fail for test: {}, \nparams {:?} {:?}",
                        test.name,
                        test.msg.clone(),
                        test.ctx.clone()
                    );
                    assert_ne!(proto_output.events.is_empty(), true); // Some events must exist.

                    // The object in the output is a ChannelEnd, should have init state.
                    let res: ChannelResult = proto_output.result;
                    assert_eq!(res.channel_end.state().clone(), State::Init);
                    let msg_init = test.msg.clone();

                    if let ChannelMsg::ChannelOpenInit(msg_init) = msg_init {
                        assert_eq!(res.port_id.clone(), msg_init.port_id.clone());
                    }

                    for e in proto_output.events.iter() {
                        assert!(matches!(e, &IBCEvent::OpenInitChannel(_)));
                    }
                }
                Err(e) => {
                    assert_eq!(
                        test.want_pass,
                        false,
                        "chan_open_init: did not pass test: {}, \nparams {:?} {:?} error: {:?}",
                        test.name,
                        test.msg,
                        test.ctx.clone(),
                        e,
                    );
                }
            }
        }
    }
}
