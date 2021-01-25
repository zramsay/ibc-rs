use super::handles::ChainHandles;

use ibc::ics04_channel::channel::Order;
use ibc::ics24_host::identifier::ChainId;

use permutator::Combination;
use relayer::channel::Channel;
use relayer::connection::Connection;
use relayer::foreign_client::ForeignClient;

use eyre::{eyre, Report, WrapErr};

use std::collections::HashMap;

const PORT: &str = "transfer";
pub struct Channels {
    channels: HashMap<(ChainId, ChainId), Channel>,
}

impl Channels {
    #[allow(dead_code)]
    pub fn setup_all_to_all(handles: ChainHandles) -> Result<Self, Report> {
        let chain_ids: Vec<_> = handles.ids().collect();
        let chain_id_pairs = chain_ids
            .combination(2)
            .map(|combination| {
                let chain_a_id = (*combination[0]).clone();
                let chain_b_id = (*combination[1]).clone();
                (chain_a_id, chain_b_id)
            })
            .collect();
        Self::setup(chain_id_pairs, handles)
    }

    pub fn setup(
        chain_id_pairs: Vec<(ChainId, ChainId)>,
        handles: ChainHandles,
    ) -> Result<Self, Report> {
        let mut channels = Self::new();
        for (chain_a_id, chain_b_id) in chain_id_pairs {
            channels.add_channel(chain_a_id, chain_b_id, &handles)?;
        }
        Ok(channels)
    }

    fn new() -> Self {
        Self {
            channels: Default::default(),
        }
    }

    fn add_channel(
        &mut self,
        chain_a_id: ChainId,
        chain_b_id: ChainId,
        handles: &ChainHandles,
    ) -> Result<(), Report> {
        let client_on_a_for_b = Self::create_client(&chain_a_id, &chain_b_id, &handles)?;
        let client_on_b_for_a = Self::create_client(&chain_b_id, &chain_a_id, &handles)?;
        let connection_a_b = Self::create_connection(client_on_a_for_b, client_on_b_for_a)?;
        let channel_a_b = Self::create_channel(connection_a_b)?;
        let key = Self::key(chain_a_id, chain_b_id);
        let result = self.channels.insert(key, channel_a_b);
        assert!(result.is_none(), "channel should not exist");
        Ok(())
    }

    fn create_client(
        chain_a_id: &ChainId,
        chain_b_id: &ChainId,
        handles: &ChainHandles,
    ) -> Result<ForeignClient, Report> {
        let chain_a_handle = handles
            .get(chain_a_id)
            .expect("handle should exist")
            .clone();
        let chain_b_handle = handles
            .get(chain_b_id)
            .expect("handle should exist")
            .clone();
        let client_on_a_for_b = ForeignClient::new(chain_a_handle, chain_b_handle)
            .wrap_err_with(|| eyre!("creating client on {} for {}", chain_a_id, chain_b_id))?;
        println!(
            "client on {} for {}: {:?}",
            chain_a_id,
            chain_b_id,
            client_on_a_for_b.id()
        );
        Ok(client_on_a_for_b)
    }

    fn create_connection(
        client_on_a: ForeignClient,
        client_on_b: ForeignClient,
    ) -> Result<Connection, Report> {
        let chain_a_id = client_on_a.dst_chain().id();
        let chain_b_id = client_on_a.src_chain().id();

        let connection_a_b = Connection::new(client_on_a, client_on_b).wrap_err_with(|| {
            eyre!(
                "creating connection between {} and {}",
                chain_a_id,
                chain_b_id
            )
        })?;
        println!(
            "connection {}-{} ids: {:?} | {:?}",
            chain_a_id,
            chain_b_id,
            connection_a_b.config.a_config.connection_id(),
            connection_a_b.config.b_config.connection_id()
        );
        Ok(connection_a_b)
    }

    fn create_channel(connection_a_b: Connection) -> Result<Channel, Report> {
        let chain_a_id = connection_a_b.config.a_config.chain_id().clone();
        let chain_b_id = connection_a_b.config.b_config.chain_id().clone();

        let ordering = Order::default();
        /*
        With `Default::default()` for ports I get the following error:
        "could not retrieve module from port-id: ports/defaultPort: capability not found"
         */
        let port_a = PORT.parse().unwrap();
        let port_b = PORT.parse().unwrap();
        let channel_a_b =
            Channel::new(connection_a_b, ordering, port_a, port_b).wrap_err_with(|| {
                eyre!("creating channel between {} and {}", chain_a_id, chain_b_id)
            })?;
        println!(
            "channel {}-{} ids: {:?} | {:?}",
            chain_a_id,
            chain_b_id,
            channel_a_b.config.a_config.channel_id(),
            channel_a_b.config.b_config.channel_id()
        );

        Ok(channel_a_b)
    }

    fn key(chain_a_id: ChainId, chain_b_id: ChainId) -> (ChainId, ChainId) {
        use std::cmp::Ordering;
        match chain_a_id.cmp(&chain_b_id) {
            Ordering::Less => (chain_a_id, chain_b_id),
            Ordering::Greater => (chain_a_id, chain_b_id),
            Ordering::Equal => panic!("chains connected by channel should be different"),
        }
    }
}
