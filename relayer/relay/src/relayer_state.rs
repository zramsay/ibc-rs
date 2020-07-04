use crate::chain_event::{BuilderEvent, BuilderObject, ChainEvent};
use crate::chain_querier::{valid_query_response, ChainQueryResponse};
use crate::config::{ChainConfig, Config};
use crate::event_handler::RelayerEvent;
use crate::message_builder::{BuilderRequests, MessageBuilder};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics24_host::identifier::ClientId;
use std::collections::HashMap;
use std::hash::Hash;
use tendermint::block::Height;
use tracing::debug;

#[derive(Debug, Clone, PartialOrd, PartialEq, Eq, Hash)]
pub struct BuilderTrigger {
    pub chain: ChainId,
    pub obj: BuilderObject,
}

impl BuilderTrigger {
    pub fn from_event(ev: ChainEvent) -> Result<Self, BoxError> {
        match ev.trigger_object {
            BuilderObject::ConnectionBuilderObject(_) => Ok(BuilderTrigger {
                chain: ev.trigger_chain,
                obj: ev.trigger_object,
            }),
            _ => Err("only connection, channels or packets should be triggers for builders".into()),
        }
    }
}

/// This is the Event handler's chain data
#[derive(Debug, Clone)]
pub struct ChainData {
    pub config: ChainConfig,
    /// Chain's height
    pub height: Height,
    /// Heights of clients instantiated on chain
    pub client_heights: HashMap<ClientId, Height>,
}

impl ChainData {
    fn new(config: &ChainConfig) -> Self {
        ChainData {
            config: config.clone(),
            height: Height::from(0),
            client_heights: HashMap::new(),
        }
    }
}
#[derive(Debug, Clone)]
pub struct RelayerState {
    chain_states: HashMap<ChainId, ChainData>,
    /// Message Builder, key is the trigger event, value shows the state of event processing
    message_builders: HashMap<BuilderTrigger, MessageBuilder>,
}

impl RelayerState {
    pub fn new(config: Config) -> Self {
        let mut res = RelayerState {
            chain_states: HashMap::new(),
            message_builders: HashMap::new(),
        };

        for chain in &config.chains {
            res.chain_states.insert(chain.id, ChainData::new(chain));
        }
        res
    }

    pub fn handshake_event_handler(
        &mut self,
        ev: &ChainEvent,
    ) -> Result<BuilderRequests, BoxError> {
        // get the destination chain from the event
        let dest_chain = self.chain_from_client(ev.trigger_object.clone().client_id()?)?;

        // check if a message builder already exists for the object,
        // return if the event is old or for a "lower" state.
        let key = BuilderTrigger::from_event(ev.clone())?;
        self.discard_event_if_higher_matching_mb(&key, ev)?;
        //self.discard_event_if_higher_matching_flipped_mb(&key, ev)?;

        if crate::chain_event::handshake_terminus_event(ev.event.clone()) {
            return Ok(BuilderRequests::new());
        }

        // create new message builder, if we are here any old builder should have been removed
        // in the handling above.
        let chains = self.chain_states.clone();
        let new_mb = self
            .message_builders
            .entry(key)
            .or_insert_with(|| MessageBuilder::new(ev, dest_chain, chains));

        new_mb.message_builder_handler(&RelayerEvent::ChainEvent(ev.clone()))
    }

    pub fn new_block_update(&mut self, ev: ChainEvent) -> Result<BuilderRequests, BoxError> {
        // Iterate over all builders in case some were waiting for this new block
        let mut merged_requests = BuilderRequests::new();
        if let Some(BuilderEvent::NewBlock) = Some(ev.event.clone()) {
            // set the chain's new height
            self.chain_states
                .get_mut(&ev.trigger_chain)
                .ok_or("unknown chain")?
                .height = ev.chain_height;

            for (chid, val) in self.chain_states.clone() {
                debug!("new chain state {}: height {}", chid, val.height);
            }

            // Iterate over message builders and send the NewBlock event to those with matching
            // source or destination chains
            for (_, mb) in self.message_builders.iter_mut() {
                let src_chain_id = mb.event.trigger_chain;
                let dest_chain_id = mb.dest_chain;
                if ev.trigger_chain == src_chain_id || ev.trigger_chain == dest_chain_id {
                    if let Ok(mut requests) =
                        mb.message_builder_handler(&RelayerEvent::ChainEvent(ev.clone()))
                    {
                        merged_requests.merge(&mut requests)
                    }
                }
            }
            return Ok(merged_requests);
        }
        Err("unexpected event".into())
    }

    pub fn query_response_handler(
        &mut self,
        response: &ChainQueryResponse,
    ) -> Result<BuilderRequests, BoxError> {
        let mut merged_requests = BuilderRequests::new();

        for (_, mb) in self.message_builders.iter_mut() {
            if valid_query_response(&response, &mb.src_queries)
                || valid_query_response(&response, &mb.dest_queries)
            {
                if let Ok(mut requests) =
                    mb.message_builder_handler(&RelayerEvent::QueryEvent(response.clone()))
                {
                    merged_requests.merge(&mut requests)
                }
            }
        }

        Err("No matching message builder for query response".into())
    }

    pub fn client_handler(&mut self, n: ChainEvent) -> Result<(), BoxError> {
        if let Some(BuilderEvent::CreateClient) = Some(n.event) {
            let key = n.trigger_object;
            *self
                .chain_states
                .get_mut(&n.trigger_chain)
                .ok_or("unknown chain")?
                .client_heights
                .entry(key.client_id()?)
                .or_insert_with(|| Height::from(0)) = key.client_height()?;
            for (chid, val) in self.chain_states.clone() {
                debug!(
                    "new chain state {}: client height {:?}",
                    chid, val.client_heights
                );
            }
            return Ok(());
        }
        Err("unexpected event".into())
    }

    fn chain_from_client(&mut self, client_id: ClientId) -> Result<ChainId, BoxError> {
        Ok(*self
            .chain_states
            .iter()
            .find(|c| {
                c.1.config
                    .client_ids
                    .iter()
                    .any(|cl| client_id == cl.parse().unwrap())
            })
            .ok_or_else(|| "missing client in configuration".to_string())?
            .0)
    }

    fn get_message_builder(&mut self, key: &BuilderTrigger) -> Option<&mut MessageBuilder> {
        self.message_builders.get_mut(key)
    }

    fn remove_message_builder(&mut self, key: &BuilderTrigger) -> Option<MessageBuilder> {
        self.message_builders.remove(key)
    }

    fn discard_for_higher_matching_mb(
        &mut self,
        key: &BuilderTrigger,
        ev: &ChainEvent,
    ) -> Result<(), BoxError> {
        debug!(
            "checking if mb: {:?} \nshould be removed due to\n {:?}",
            key, ev
        );

        if let Some(existing_mb) = self.get_message_builder(key) {
            // a message builder exists for the new event
            if existing_mb.event.event >= ev.event
                || existing_mb.event.chain_height > ev.chain_height
            {
                debug!("don't remove mb");
                return Err("message builder in higher state exists".into());
            }
            // A new event with the object in a "higher" state is received
            // Cancel old message builder by removing it from the state.
            // Any pending request responses will be discarded
            debug!("removing mb");
            self.remove_message_builder(&key);

            debug!("\n\nSTATE DUMP {:?}\n\n", self.message_builders);
        }
        Ok(())
    }

    fn discard_event_if_higher_matching_mb(
        &mut self,
        key: &BuilderTrigger,
        ev: &ChainEvent,
    ) -> Result<(), BoxError> {
        self.discard_for_higher_matching_mb(&key, ev)?;

        // flip the key if possible
        // TODO - figure out client_id() for channel and packet
        let dest_chain = self.chain_from_client(ev.trigger_object.clone().client_id()?)?;
        match ev.trigger_object.flipped() {
            Ok(obj) => {
                let flipped_key = BuilderTrigger {
                    chain: dest_chain,
                    obj,
                };
                self.discard_for_higher_matching_mb(&flipped_key, ev)
            }
            Err(_) => Ok(()),
        }
    }
}
