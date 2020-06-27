use crate::chain_querier::{
    valid_query_response, QueryClientConsensus, QueryConnectionEnd, QueryRequest, QueryResponse,
};
use crate::config::{ChainConfig, Config};
use crate::event_handler::{BuilderObject, BuilderTrigger, ConnectionEventObject};
use crate::light_client_querier::{ConsensusStateUpdateRequestParams, LightClientRequest};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics02_client::events as ClientEvents;
use relayer_modules::ics02_client::events::NewBlock;
use relayer_modules::ics03_connection::exported::State;
use relayer_modules::ics24_host::identifier::ClientId;
use std::collections::HashMap;
use tendermint::block::Height;

const MAX_HEIGHT_GAP: u64 = 100;

#[derive(Debug, Clone)]
pub(crate) struct BuilderRequests {
    // queries
    pub src_queries: Vec<QueryRequest>,
    pub dest_queries: Vec<QueryRequest>,

    // local light client requests
    pub src_client_request: Option<LightClientRequest>,
    pub dest_client_request: Option<LightClientRequest>,
}

impl BuilderRequests {
    fn new() -> Self {
        BuilderRequests {
            src_queries: vec![],
            dest_queries: vec![],
            src_client_request: None,
            dest_client_request: None,
        }
    }
    fn merge(&mut self, br: &mut BuilderRequests) {
        self.src_queries.append(&mut br.src_queries);
        self.dest_queries.append(&mut br.dest_queries);
        // TODO - change client requests from Option to Vec
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
enum BuilderState {
    ConnectionState(State),
}

pub struct MessageBuilder<CS> {
    state: BuilderState,
    src_chain: ChainId,
    src_height: Height,
    pub dest_chain: ChainId,

    // wait for src chain to get to src_height
    src_height_needed: Height,

    // pending queries
    src_queries: Vec<QueryRequest>,
    src_responses: Vec<QueryResponse<CS>>,
    dest_queries: Vec<QueryRequest>,
    dest_responses: Vec<QueryResponse<CS>>,

    // pending requests to local light clients
    src_client_request: Option<LightClientRequest>,
    dest_client_request: Option<LightClientRequest>,
}

impl<CS> MessageBuilder<CS> {
    fn new(
        src_chain: ChainId,
        src_height: Height,
        state: BuilderState,
        dest_chain: ChainId,
    ) -> Self {
        MessageBuilder {
            state,
            src_chain,
            src_height,
            dest_chain,
            src_height_needed: Height::from(0),
            src_queries: vec![],
            src_responses: vec![],
            dest_queries: vec![],
            dest_responses: vec![],
            src_client_request: None,
            dest_client_request: None,
        }
    }
}

/// This is the Event handler's chain data
#[derive(Debug, Clone)]
struct ChainData {
    config: ChainConfig,
    /// Chain's height
    height: Height,
    /// Heights of clients instantiated on chain
    client_heights: HashMap<ClientId, Height>,
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

pub(crate) struct RelayerState<CS> {
    chain_states: HashMap<ChainId, ChainData>,
    /// Message Builder, key is the trigger event, value shows the state of event processing
    message_builders: HashMap<BuilderTrigger, MessageBuilder<CS>>,
}

impl<CS> RelayerState<CS> {
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

    pub fn new_block_update(&mut self, source: ChainId, nb: NewBlock) -> Result<(), BoxError> {
        self.chain_states
            .get_mut(&source)
            .ok_or("unknown chain")?
            .height = nb.height;

        // Iterate over all builders in case some were waiting for this new block
        let mut merged_requests = BuilderRequests::new();
        let keys: Vec<BuilderTrigger> = self
            .message_builders
            .iter()
            .map(|(k, _)| k.clone())
            .collect();
        for key in keys {
            match self.message_builder_next_step(key.clone()) {
                Ok(mut requests) => merged_requests.merge(&mut requests),
                Err(_) => {
                    continue;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn query_response_handler(
        &mut self,
        from_chain: ChainId,
        trigger: BuilderTrigger,
        response: QueryResponse<CS>,
    ) -> Result<(), BoxError> {
        if let Some(mb) = self.get_message_builder(&trigger) {
            if from_chain == mb.src_chain && valid_query_response(&response, &mb.src_queries) {
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

    // TODO - this should become client_handler(), i.e. merge the create and update once
    // the events are reorg-ed
    pub(crate) fn create_client_handler(
        &mut self,
        source: ChainId,
        cc: ClientEvents::CreateClient,
    ) -> Result<(), BoxError> {
        *self
            .chain_states
            .get_mut(&source)
            .ok_or("unknown chain")?
            .client_heights
            .entry(cc.client_id)
            .or_insert_with(|| Height::from(0)) = cc.client_height;
        Ok(())
    }

    pub(crate) fn update_client_handler(
        &mut self,
        source: ChainId,
        cu: ClientEvents::UpdateClient,
    ) -> Result<(), BoxError> {
        *self
            .chain_states
            .get_mut(&source)
            .ok_or("unknown chain")?
            .client_heights
            .entry(cu.client_id)
            .or_insert_with(|| Height::from(0)) = cu.client_height;
        Ok(())
    }

    pub(crate) fn connection_handler(
        &mut self,
        src_chain: ChainId,
        height: Height,
        state: State,
        conn: ConnectionEventObject,
    ) -> Result<BuilderRequests, BoxError> {
        // get the destination chain and its latest height
        let dest_chain = self.chain_from_client(conn.client_id.clone())?;
        let dest_chain_height = self.latest_chain_height(dest_chain)?;
        // get the height of client on src, client of destination chain

        // check if a message builder already exists for the connection,
        // return if the update is old or for a "lower" state.
        if self.duplicate_message_builder_handler(
            &BuilderTrigger {
                trigger_chain: src_chain,
                trigger_object: BuilderObject::ConnectionEvent(conn.clone()),
            },
            BuilderState::ConnectionState(state.clone()),
            height,
        ) || self.duplicate_message_builder_handler(
            &BuilderTrigger {
                trigger_chain: dest_chain,
                trigger_object: BuilderObject::ConnectionEvent(conn.clone().flipped()),
            },
            BuilderState::ConnectionState(state.clone()),
            dest_chain_height,
        ) {
            return Err("Received a past event, discard".into());
        }

        // create new message builder, if we are here any duplicates should have been removed
        // in the handling above.
        let key = BuilderTrigger {
            trigger_chain: src_chain,
            trigger_object: BuilderObject::ConnectionEvent(conn),
        };

        self.message_builders.entry(key.clone()).or_insert_with(|| {
            MessageBuilder::new(
                src_chain,
                height,
                BuilderState::ConnectionState(state),
                dest_chain,
            )
        });

        self.message_builder_next_step(key)
    }

    pub(crate) fn message_builder_next_step(
        &mut self,
        key: BuilderTrigger,
    ) -> Result<BuilderRequests, BoxError> {
        let src_chain = self.get_mb_src_chain(key.clone())?;
        let dest_chain = self.get_mb_dest_chain(key.clone())?;

        let src_chain_height = self.latest_chain_height(src_chain)?;
        let src_client_on_dest_height: Height = self.client_height(
            dest_chain,
            key.clone().get_trigger_counterparty_client_id()?,
        )?;

        let dest_chain_height = self.latest_chain_height(dest_chain)?;
        let dest_client_on_src_height: Height =
            self.client_height(src_chain, key.clone().get_trigger_client_id()?)?;

        let mb = self.message_builders.get_mut(&key).unwrap();

        // check if client on source chain is "fresh", i.e. within MAX_HEIGHT_GAP of dest_chain
        if Height::from(dest_client_on_src_height.value() + MAX_HEIGHT_GAP) <= dest_chain_height
            && mb.dest_client_request.is_none()
        {
            // build request for new header(s) from local light client for destination chain
            mb.dest_client_request = Option::from(LightClientRequest::ConsensusStateUpdateRequest(
                ConsensusStateUpdateRequestParams::new(
                    mb.dest_chain,
                    dest_chain_height,
                    dest_client_on_src_height,
                ),
            ));
        } else if mb.src_queries.is_empty() {
            // plan queries for the source chain
            mb.src_queries.push(QueryRequest::ClientConsensusRequest(
                QueryClientConsensus::new(
                    mb.src_chain,
                    mb.src_height,
                    key.clone().get_trigger_client_id()?,
                    true,
                ),
            ));
            mb.src_queries
                .push(QueryRequest::ConnectionEndRequest(QueryConnectionEnd::new(
                    mb.src_chain,
                    mb.src_height,
                    key.clone().get_trigger_connection_id()?,
                    true,
                )));
        }

        if src_chain_height <= mb.src_height {
            // flag the wait for source chain to create block height+1
            mb.src_height_needed = mb.src_height.increment();
        } else {
            // source chain has height + 1, update client on destination with that value
            if src_client_on_dest_height < mb.src_height && mb.src_client_request.is_none() {
                // client on destination needs update and there is no pending request,
                // request header from local source light client
                mb.src_client_request =
                    Option::from(LightClientRequest::ConsensusStateUpdateRequest(
                        ConsensusStateUpdateRequestParams::new(
                            mb.src_chain,
                            mb.src_height.increment(),
                            src_client_on_dest_height,
                        ),
                    ));
            }
        }

        // start query on destination chain if needed
        if mb.src_queries.is_empty() {
            mb.dest_queries
                .push(QueryRequest::ConnectionEndRequest(QueryConnectionEnd::new(
                    mb.dest_chain,
                    Height::from(0),
                    key.clone().get_trigger_counterparty_connection_id()?,
                    true,
                )));
        }

        // return all requests to event handler for IO
        Ok(BuilderRequests {
            src_queries: mb.src_queries.clone(),
            dest_queries: mb.dest_queries.clone(),
            src_client_request: mb.src_client_request.clone(),
            dest_client_request: mb.dest_client_request.clone(),
        })
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

    fn get_message_builder(&mut self, key: &BuilderTrigger) -> Option<&mut MessageBuilder<CS>> {
        self.message_builders.get_mut(key)
    }

    fn remove_message_builder(&mut self, key: &BuilderTrigger) -> Option<MessageBuilder<CS>> {
        self.message_builders.remove(key)
    }

    fn duplicate_message_builder_handler(
        &mut self,
        key: &BuilderTrigger,
        state: BuilderState,
        height: Height,
    ) -> bool {
        if let Some(existing_mb) = self.get_message_builder(key) {
            if existing_mb.state >= state || existing_mb.src_height > height {
                return true;
            }
            // A new event with the object in a "higher" state is received
            // Cancel old message builder by removing it from the state.
            // Any pending request responses will be discarded
            self.remove_message_builder(&key);
        }
        false
    }

    fn get_mb_src_chain(&mut self, key: BuilderTrigger) -> Result<ChainId, BoxError> {
        Ok(self
            .message_builders
            .get_mut(&key)
            .ok_or("Invalid chain")?
            .src_chain)
    }

    fn get_mb_dest_chain(&mut self, key: BuilderTrigger) -> Result<ChainId, BoxError> {
        Ok(self
            .message_builders
            .get_mut(&key)
            .ok_or("Invalid chain")?
            .dest_chain)
    }
}
