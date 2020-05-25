/// Event Listenr integration tests.
///
/// These are all ignored by default, since they test against running
/// against a running IBC network. This can be setup by running `./dev-env` in github.com/iqlusioninc/relayer
///
/// ```
/// cargo test -- --ignored
/// ```

mod ibc_events {
    use relayer_modules::events::IBCEvent;
    use tendermint::rpc::event_listener::EventListener;

    async fn create_event_listener() -> EventListener {
        tendermint::rpc::event_listener::EventListener::connect(
            "tcp://127.0.0.1:26657".parse().unwrap(),
        )
        .await
        .unwrap()
    }

    /// Create Client qevent
    #[tokio::test]
    // #[ignore]
    async fn test_create_client_event() {
        let mut client = create_event_listener().await;
        let _ = client.subscribe(tendermint::rpc::event_listener::EventSubscription::TransactionSubscription).await.unwrap();

        let mut x: i32 = 0;
        loop {
                match client.get_event().await{
                    Ok(Some(y)) =>{
                        let events = IBCEvent::get_all_events(y);
                        if events.len() != 0 {
                            dbg!(events);
                        }

                        x += 1;
            
                    },
                    Err(z)=>{
                        
                        dbg!(z);
                        x +=1;
                    }
                    _=>{},

                }
                    if x == 50 {
                        panic!("No Create Client Event found")
                    }
        }
    }
}
