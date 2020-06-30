use crate::chain_event::{BuilderEvent, ChainEvent};
use crate::chain_querier::{ChainQueryRequestParams, ChainQueryResponse, chain_query_consensus_state_request, chain_query_object_request, chain_query_flipped_object_request};
use crate::event_handler::RelayerEvent;
use crate::light_client_querier::{LightClientQuery, light_client_headers_request};
use crate::relayer_state::{BuilderObject, ChainData};
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use tendermint::block::Height;

const MAX_HEIGHT_GAP: u64 = 100;

#[derive(Debug, Clone)]
enum BuilderState {
    Init,
    UpdatingClientBonA,
    WaitNextHeightOnA,
    SendingUpdateClientBtoA,
    UpdatingClientAonB,
    SendingUpdateClientAtoB,
    QueryingObjects,
    SendingTransactionToB,
    Finished,
}

#[derive(Debug, Clone)]
pub struct MessageBuilder {
    fsm_state: BuilderState,

    // the event that created this builder, only its height may change
    pub event: ChainEvent,
    pub dest_chain: ChainId,

    // wait for src chain to get to src_height
    src_height_needed: Height,

    // pending queries
    pub src_queries: Vec<ChainQueryRequestParams>,
    pub src_responses: Vec<ChainQueryResponse>,
    pub dest_queries: Vec<ChainQueryRequestParams>,
    pub dest_responses: Vec<ChainQueryResponse>,

    // pending requests to local light clients
    src_client_request: Option<LightClientQuery>,
    dest_client_request: Option<LightClientQuery>,
}

impl MessageBuilder {
    pub fn new(event: &ChainEvent, dest_chain: ChainId) -> Self {
        MessageBuilder {
            fsm_state: BuilderState::Init,
            event: event.clone(),
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

    pub fn message_builder_handler(
        &mut self,
        event: RelayerEvent,
        src_chain: &ChainData,
        dest_chain: &ChainData,
    ) -> Result<BuilderRequests, BoxError> {
        // TODO - look at errors and decide, most of them should be just recorded as the state machine should not have changed
        let (new_state, requests) = match self.fsm_state {
            BuilderState::Init => self.init_state_handle(event, src_chain, dest_chain)?,
            BuilderState::WaitNextHeightOnA => {
                self.wait_next_src_height_state_handle(event, src_chain, dest_chain)?
            }
            //            BuilderState::UpdatingClientBonA => self.handle.update_src_client_state_handle(key, event, chains),
            //            BuilderState::SendingUpdateClientBtoA => self.handle.tx_src_client_state_handle(key, event, chains),
            //            BuilderState::UpdatingClientAonB => self.handle.update_dest_client_state_handle(key, event, chains),
            //            BuilderState::SendingUpdateClientAtoB => self.handle.tx_dest_client_state_handle(key, event, chains),
            //            BuilderState::QueryTriggerObjects => self.handle.query_objects_state_handle(key, event, chains),
            //            BuilderState::SendingTransactionToB => self.handle.sending_transaction_to_dest_handle(key, event, chains),
            _ => (self.fsm_state.clone(), BuilderRequests::new()),
        };
        self.fsm_state = new_state;
        Ok(requests)
    }

    // called immediately after builder is created
    fn init_state_handle(
        &mut self,
        event: RelayerEvent,
        a: &ChainData,
        b: &ChainData,
    ) -> Result<(BuilderState, BuilderRequests), BoxError> {
        let mut new_state = self.fsm_state.clone();
        let mut requests = BuilderRequests::new();

        match event {
            RelayerEvent::ChainEvent(ch_ev) => {
                let obj = ch_ev.trigger_object.ok_or("event with no object")?;

                if crate::chain_event::requires_updated_b_client_on_a(ch_ev.event) {
                    let b_height = b.height;
                    let b_client_on_a_height = a.client_heights[&obj.client_id()];

                    // check if client on source chain is "fresh", i.e. within MAX_HEIGHT_GAP of dest_chain
                    if Height::from(b_client_on_a_height.value() + MAX_HEIGHT_GAP) <= b_height {
                        // build request for new header(s) from local light client for destination chain
                        self.dest_client_request = light_client_headers_request(
                            self.dest_chain,
                            b_height,
                        b_client_on_a_height);

                        // return requests to event handler for IO
                        new_state = BuilderState::UpdatingClientBonA;
                        requests = BuilderRequests {
                            dest_client_request: self.dest_client_request.clone(),
                            ..requests.clone()
                        };
                        return Ok((new_state, requests));
                    }
                }

                if a.height <= self.event.chain_height {
                    // IBC events typically come before the corresponding NewBlock event and
                    // is therefore possible that the recorded height of A is smaller (strict) than
                    // the height of the message builder (created by the IBC Event).
                    new_state = BuilderState::WaitNextHeightOnA;
                } else {
                    // a_height > self.src_height - this is not possible as this means we got events
                    // out of order, i.e. NewBlock(H), IBCEvent(X, h) with h < H
                    Err("events out of order".into())
                }
            }
            _ => {}
        }

        Ok((new_state.clone(), BuilderRequests::new()))
    }

    fn wait_next_src_height_state_handle(
        &mut self,
        event: RelayerEvent,
        a: &ChainData,
        b: &ChainData,
    ) -> Result<(BuilderState, BuilderRequests), BoxError> {
        let mut new_state = self.fsm_state.clone();
        let mut requests = BuilderRequests::new();

        let obj = self
            .event
            .trigger_object
            .clone()
            .ok_or("event with no object")?;

        match event {
            RelayerEvent::ChainEvent(chain_ev) => {
                if let BuilderEvent::NewBlock = chain_ev.event {
                    // Only interested in new blocks for source chain
                    if a.config.id != self.event.trigger_chain {
                        return Ok((new_state, requests));
                    }

                    let a_height = a.height;
                    let a_client_on_b_height = b.client_heights[&obj.counterparty_client_id()];

                    if a_height > self.event.chain_height {
                        if a_client_on_b_height <= self.event.chain_height &&
                            self.src_client_request.is_none() {
                            // if client on destination needs update and we haven't requested them already,
                            // request header(s) from local source light client.
                            self.src_client_request = light_client_headers_request(
                                    self.event.trigger_chain,
                                    self.event.chain_height.increment(),
                                    a_height);

                            new_state = BuilderState::UpdatingClientBonA;
                            requests = BuilderRequests {
                                dest_client_request: self.dest_client_request.clone(),
                                ..requests.clone()
                            };
                        } else {
                            self.event.chain_height = Height(u64::from(a_client_on_b_height) - 1);
                            // plan queries for the source chain
                            // query consensus state if required by the event
                            if crate::chain_event::requires_consensus_proof_for_b_client_on_a(chain_ev.event) {
                                self.src_queries.push(chain_query_consensus_state_request(
                                    self.event.trigger_chain,
                                    self.event.chain_height,
                                    obj.client_id().clone(), a.client_heights[&obj.client_id()],
                                    true,
                                ))
                            }
                            // query the builder object, e.g. connection, channel, etc
                            self.src_queries.push(chain_query_object_request(&self.event, true));

                            // query object on destination chain if applicable (e.g. for connections
                            // and channels).
                            if let Some(dest_query) = chain_query_flipped_object_request(&self.event, false) {
                                self.src_queries.push(dest_query);
                            }

                            new_state = BuilderState::QueryingObjects;
                            requests = BuilderRequests {
                                src_queries: self.src_queries.clone(),
                                dest_queries: self.dest_queries.clone(),
                                ..requests.clone()
                            };
                        }
                    } else if a_height == self.event.chain_height {
                        // it is possible to get the new block event immediately after the
                        // trigger event, nothing to do
                    } else {
                        Err("event suggests that blockchain is decreasing in height".into());
                    }
                }
            }
            _ => {}
        }
        Ok((new_state, requests))
    }
}

#[derive(Debug, Clone)]
pub struct BuilderRequests {
    // queries
    pub src_queries: Vec<ChainQueryRequestParams>,
    pub dest_queries: Vec<ChainQueryRequestParams>,

    // local light client requests
    pub src_client_request: Option<LightClientQuery>,
    pub dest_client_request: Option<LightClientQuery>,
}

impl BuilderRequests {
    pub fn new() -> Self {
        BuilderRequests {
            src_queries: vec![],
            dest_queries: vec![],
            src_client_request: None,
            dest_client_request: None,
        }
    }

    pub fn merge(&mut self, br: &mut BuilderRequests) {
        self.src_queries.append(&mut br.src_queries);
        self.dest_queries.append(&mut br.dest_queries);
        // TODO - change client requests from Option to Vec
    }
}
