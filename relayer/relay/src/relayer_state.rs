use crate::chain_event::{BuilderEvent, ChainEvent};
use crate::chain_querier::{valid_query_response, ChainQueryResponse};
use crate::config::{ChainConfig, Config};
use crate::event_handler::RelayerEvent;
use crate::message_builder::{BuilderRequests, MessageBuilder};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics24_host::identifier::ClientId;
use relayer_modules::query::{IbcQuery, IbcResponse};
use std::collections::HashMap;
use tendermint::block::Height;

pub(crate) trait BuilderObject: Sized {
    fn flipped(&self) -> Option<Self> {
        None
    }
    fn client_id(&self) -> ClientId;
    fn client_height(&self) -> Height;
    fn counterparty_client_id(&self) -> ClientId;
    fn build_ibc_query<T>(&self, height: Height, prove: bool) -> &dyn IbcQuery<Response = T>;
    fn build_flipped_ibc_query<T>(
        &self,
        height: Height,
        prove: bool,
    ) -> &dyn IbcQuery<Response = T>;
}

pub(crate) struct BuilderTrigger<O>
where
    O: BuilderObject,
{
    pub chain: ChainId,
    pub obj: O,
}

impl<O> BuilderTrigger<O>
where
    O: BuilderObject,
{
    pub fn from_event<E>(ev: ChainEvent<O>) -> Self {
        BuilderTrigger {
            chain: ev.trigger_chain,
            obj: ev.trigger_object,
        }
    }
}

/// This is the Event handler's chain data
#[derive(Debug, Clone)]
pub struct ChainData {
    pub config: ChainConfig,
    /// Chain's height
    pub(crate) height: Height,
    /// Heights of clients instantiated on chain
    pub(crate) client_heights: HashMap<ClientId, Height>,
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

pub(crate) struct RelayerState<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    chain_states: HashMap<ChainId, ChainData>,
    /// Message Builder, key is the trigger event, value shows the state of event processing
    message_builders: HashMap<BuilderTrigger<O>, MessageBuilder<O, Q>>,
}

impl<O, Q> RelayerState<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    pub(crate) fn new(config: Config) -> Self {
        let mut res = RelayerState {
            chain_states: HashMap::new(),
            message_builders: HashMap::new(),
        };

        for chain in &config.chains {
            res.chain_states.insert(chain.id, ChainData::new(chain));
        }
        res
    }

    pub fn new_block_update(&mut self, ev: ChainEvent<O>) -> Result<(), BoxError> {
        // Iterate over all builders in case some were waiting for this new block
        let mut merged_requests = BuilderRequests::new();
        //        let keys: Vec<BuilderTrigger<O>> = self
        //            .message_builders
        //            .iter()
        //            .map(|(k, _)| k.clone())
        //            .collect();
        //        for key in keys {
        //            match self.message_builder_next_step(key.clone()) {
        //                Ok(mut requests) => merged_requests.merge(&mut requests),
        //                Err(_) => {
        //                    continue;
        //                }
        //            }
        //        }
        if let Some(BuilderEvent::NewBlock) = Some(ev.event) {
            // set the chain's new height
            self.chain_states
                .get_mut(&ev.trigger_chain)
                .ok_or("unknown chain")?
                .height = ev.chain_height;

            // Iterate over message builders and send the NewBlock event to those with matching
            // source or destination chains
            for (key, mut mb) in self.message_builders {
                let src_chain_id = mb.event.trigger_chain;
                let dest_chain_id = mb.dest_chain;
                if ev.trigger_chain == src_chain_id || ev.trigger_chain == dest_chain_id {
                    let src_chain = self
                        .chain_states
                        .get(&mb.event.trigger_chain)
                        .ok_or("unknown chain")?;
                    let dest_chain = self
                        .chain_states
                        .get(&mb.dest_chain)
                        .ok_or("unknown chain")?;

                    match mb.message_builder_handler(
                        RelayerEvent::ChainEvent(ev),
                        src_chain,
                        dest_chain,
                    ) {
                        Ok(mut requests) => merged_requests.merge(&mut requests),
                        Err(_) => continue,
                    }
                }
            }
        }
        Err("unexpected event".into())
    }

    pub(crate) fn query_response_handler(
        &mut self,
        from_chain: ChainId,
        trigger: BuilderTrigger<O>,
        response: ChainQueryResponse<O, Q>,
    ) -> Result<(), BoxError> {
        if let Some(mb) = self.get_message_builder(&trigger) {
            if from_chain == mb.event.trigger_chain
                && valid_query_response(&response, &mb.src_queries)
            {
                mb.src_responses.push(response);
                return Ok(());
            } else if from_chain == mb.dest_chain
                && valid_query_response(&response, &mb.dest_queries)
            {
                mb.dest_responses.push(response);
                return Ok(());
            }
            return Err("No matching request for query response".into());
        }
        Err("No matching message builder for query response".into())
    }

    pub(crate) fn client_handler(&mut self, n: ChainEvent<O>) -> Result<(), BoxError> {
        if let Some(BuilderEvent::CreateClient) = Some(n.event) {
            let key = n.trigger_object.ok_or("missing object")?;
            *self
                .chain_states
                .get_mut(&n.trigger_chain)
                .ok_or("unknown chain")?
                .client_heights
                .entry(key.client_id())
                .or_insert_with(|| Height::from(0)) = key.client_height();
            Ok(())
        }
        Err("unexpected event".into())
    }

    pub(crate) fn handshake_event_handler(
        &mut self,
        ev: ChainEvent<O>,
    ) -> Result<BuilderRequests<O, Q>, BoxError> {
        // get the destination chain from the event
        let dest_chain = self.chain_from_client(ev.trigger_object.get_trigger_client_id())?;

        // check if a message builder already exists for the object,
        // return if the event is old or for a "lower" state.
        // TODO - do the same check for flipped version
        let key = BuilderTrigger::from_event(ev);
        if self.keep_existing_message_builder(&key, &ev) {
            return Err("Received a past event, discard".into());
        }
        // create new message builder, if we are here any old builder should have been removed
        // in the handling above.
        let new_mb = self
            .message_builders
            .entry(key.clone())
            .or_insert_with(|| MessageBuilder::new(ev, dest_chain));

        let src_chain = self
            .chain_states
            .get(&ev.trigger_chain)
            .ok_or("unknown chain")?;
        let dest_chain = self.chain_states.get(&dest_chain).ok_or("unknown chain")?;

        new_mb.message_builder_handler(RelayerEvent::ChainEvent(ev.clone()), src_chain, dest_chain)
    }

    /// get the height of client on a chain
    fn client_height(&mut self, ch: ChainId, client_id: ClientId) -> Result<Height, BoxError> {
        Ok(self
            .chain_states
            .get(&ch)
            .ok_or("unknown chain")?
            .client_heights[&client_id])
    }

    /// get the latest chain height
    fn latest_chain_height(&mut self, ch: ChainId) -> Result<Height, BoxError> {
        Ok(self.chain_states.get(&ch).ok_or("unknown chain")?.height)
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

    fn get_message_builder(
        &mut self,
        key: &BuilderTrigger<O>,
    ) -> Option<&mut MessageBuilder<O, Q>> {
        self.message_builders.get_mut(key)
    }

    fn remove_message_builder(&mut self, key: &BuilderTrigger<O>) -> Option<MessageBuilder<O, Q>> {
        self.message_builders.remove(key)
    }

    fn keep_existing_message_builder(
        &mut self,
        key: &BuilderTrigger<O>,
        ev: &ChainEvent<O>,
    ) -> bool {
        if let Some(existing_mb) = self.get_message_builder(key) {
            if existing_mb.event.event >= ev.event
                || existing_mb.event.chain_height > ev.chain_height
            {
                return true;
            }
            // A new event with the object in a "higher" state is received
            // Cancel old message builder by removing it from the state.
            // Any pending request responses will be discarded
            self.remove_message_builder(&key);
        }
        false
    }

    fn get_mb_src_chain(&mut self, key: BuilderTrigger<O>) -> Result<ChainId, BoxError> {
        Ok(self
            .message_builders
            .get_mut(&key)
            .ok_or("Invalid chain")?
            .src_chain)
    }

    fn get_mb_dest_chain(&mut self, key: BuilderTrigger<O>) -> Result<ChainId, BoxError> {
        Ok(self
            .message_builders
            .get_mut(&key)
            .ok_or("Invalid chain")?
            .dest_chain)
    }
}
