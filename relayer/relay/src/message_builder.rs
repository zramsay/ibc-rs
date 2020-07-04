use crate::chain_event::{BuilderEvent, ChainEvent};
use crate::chain_querier::{
    chain_query_consensus_state_request, chain_query_flipped_object_request,
    chain_query_object_request, ChainQueryRequestParams, ChainQueryResponse,
};
use crate::event_handler::RelayerEvent;
use crate::light_client_querier::{light_client_headers_request, LightClientQuery};
use crate::relayer_state::ChainData;
use ::tendermint::chain::Id as ChainId;
use anomaly::BoxError;
use relayer_modules::ics24_host::identifier::ClientId;
use std::collections::HashMap;
use tendermint::block::Height;
use tracing::debug;

const MAX_HEIGHT_GAP: u64 = 100;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuilderState {
    Init,
    UpdatingLocalClientB,
    SendingUpdateClientBtoA,
    WaitNextHeightOnA,
    UpdatingLocalClientA,
    SendingUpdateClientAtoB,
    QueryingObjects,
    SendingTransactionToB,
    Finished,
}

#[derive(Debug, Clone)]
pub struct MessageBuilder {
    pub fsm_state: BuilderState,
    pub chain_states: HashMap<ChainId, ChainData>,

    // the event that created this builder, only its height may change
    pub event: ChainEvent,
    pub dest_chain: ChainId,

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
    pub fn new(
        event: &ChainEvent,
        dest_chain: ChainId,
        chain_states: HashMap<ChainId, ChainData>,
    ) -> Self {
        MessageBuilder {
            fsm_state: BuilderState::Init,
            chain_states,
            event: event.clone(),
            dest_chain,
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
        event: &RelayerEvent,
    ) -> Result<BuilderRequests, BoxError> {
        // TODO - look at errors and decide, most of them should be just recorded as the state machine should not have changed

        // For NewBlock and client updates, update the chain and client heights regardless of state
        if let Some(RelayerEvent::ChainEvent(ev)) = Some(event) {
            match ev.event {
                BuilderEvent::NewBlock => {
                    self.chain_states
                        .get_mut(&ev.trigger_chain)
                        .ok_or("unknown chain")?
                        .height = ev.chain_height
                }

                BuilderEvent::CreateClient | BuilderEvent::UpdateClient => {
                    let key = &ev.trigger_object;
                    *self
                        .chain_states
                        .get_mut(&ev.trigger_chain)
                        .ok_or("unknown chain")?
                        .client_heights
                        .entry(key.client_id()?)
                        .or_insert_with(|| Height::from(0)) = key.client_height()?;
                }
                _ => {}
            }
        }

        let (new_state, requests) = match self.fsm_state {
            BuilderState::Init => self.init_state_handle(event.clone())?,
            BuilderState::WaitNextHeightOnA => {
                self.wait_next_src_height_state_handle(event.clone())?
            }

            //            BuilderState::UpdatingClientBonA => self.handle.update_src_client_state_handle(key, event, chains),
            //            BuilderState::SendingUpdateClientBtoA => self.handle.tx_src_client_state_handle(key, event, chains),
            //            BuilderState::UpdatingClientAonB => self.handle.update_dest_client_state_handle(key, event, chains),
            //            BuilderState::SendingUpdateClientAtoB => self.handle.tx_dest_client_state_handle(key, event, chains),
            //            BuilderState::QueryTriggerObjects => self.handle.query_objects_state_handle(key, event, chains),
            //            BuilderState::SendingTransactionToB => self.handle.sending_transaction_to_dest_handle(key, event, chains),
            _ => (self.fsm_state, BuilderRequests::new()),
        };
        let old_state = self.fsm_state;
        self.fsm_state = new_state;

        if new_state != old_state {
            debug!("\nXXXX new mb {:?}", self);
        }

        Ok(requests)
    }

    // called immediately after builder is created
    fn init_state_handle(
        &mut self,
        event: RelayerEvent,
    ) -> Result<(BuilderState, BuilderRequests), BoxError> {
        let mut new_state = self.fsm_state;
        let mut requests = BuilderRequests::new();

        let a = self
            .chain_states
            .get(&self.event.trigger_chain)
            .ok_or("unknown chain")?;
        // TODO - for channels and packets this needs to trigger a query
        let b_chain_id = self.chain_from_client(self.event.trigger_object.clone().client_id()?)?;
        self.dest_chain = b_chain_id;
        let b = self.chain_states.get(&b_chain_id).ok_or("unknown chain")?;
        // TODO - cleanup all other chain_states entries except source and dest

        match event {
            RelayerEvent::ChainEvent(ch_ev) => {
                let obj = ch_ev.trigger_object;

                if crate::chain_event::requires_updated_b_client_on_a(ch_ev.event) {
                    let b_height = b.height;
                    let b_client_on_a_height = a.client_heights[&obj.client_id()?];

                    // check if client on source chain is "fresh", i.e. within MAX_HEIGHT_GAP of dest_chain
                    if Height::from(b_client_on_a_height.value() + MAX_HEIGHT_GAP) <= b_height {
                        // build request for new header(s) from local light client for destination chain
                        self.dest_client_request = light_client_headers_request(
                            self.dest_chain,
                            b_height,
                            b_client_on_a_height,
                        );

                        // return requests to event handler for IO
                        new_state = BuilderState::UpdatingLocalClientB;
                        requests = BuilderRequests {
                            dest_client_request: self.dest_client_request.clone(),
                            ..requests.clone()
                        };
                        return Ok((new_state, requests));
                    }
                }

                if a.height <= self.event.chain_height {
                    // IBC events typically come before the corresponding NewBlock event and it is
                    // therefore possible that the recorded height of A is smaller (strict) than
                    // the height of the message builder (created by the IBC Event).
                    new_state = BuilderState::WaitNextHeightOnA;
                } else {
                    // a_height > self.src_height - this is not possible as this means we got events
                    // out of order, i.e. NewBlock(H), IBCEvent(X, h) with h < H
                    return Err("events out of order".into());
                }
            }
            _ => {}
        }

        Ok((new_state, BuilderRequests::new()))
    }

    fn wait_next_src_height_state_handle(
        &mut self,
        event: RelayerEvent,
    ) -> Result<(BuilderState, BuilderRequests), BoxError> {
        let mut new_state = self.fsm_state;
        let mut requests = BuilderRequests::new();

        let obj = self.event.trigger_object.clone();
        let a = self
            .chain_states
            .get(&self.event.trigger_chain)
            .ok_or("unknown chain")?;
        let b = self
            .chain_states
            .get(&self.dest_chain)
            .ok_or("unknown chain")?;

        match event {
            RelayerEvent::ChainEvent(chain_ev) => {
                // Only interested in new block event
                if BuilderEvent::NewBlock != chain_ev.event {
                    return Err("event is ignored".into());
                }

                // Only interested in higher new block for source chain
                if a.config.id != self.event.trigger_chain || a.height == self.event.chain_height {
                    // it is possible to get the new block event immediately after the
                    // trigger event, nothing to do
                    return Ok((new_state, requests));
                }
                if a.height < self.event.chain_height {
                    return Err("event suggests that blockchain is decreasing in height".into());
                }

                let a_client_on_b_height = b.client_heights[&obj.counterparty_client_id()?];

                if a_client_on_b_height <= self.event.chain_height
                //&& self.src_client_request.is_none()
                {
                    // if client on destination needs update and we haven't requested them already,
                    // request header(s) from local source light client.
                    self.src_client_request = light_client_headers_request(
                        self.event.trigger_chain,
                        self.event.chain_height.increment(),
                        a_client_on_b_height,
                    );

                    new_state = BuilderState::UpdatingLocalClientA;
                    requests = BuilderRequests {
                        dest_client_request: self.dest_client_request.clone(),
                        ..requests.clone()
                    };
                } else {
                    self.event.chain_height = Height(u64::from(a_client_on_b_height) - 1);
                    // plan queries for the source chain
                    // query consensus state if required by the event
                    if crate::chain_event::requires_consensus_proof_for_b_client_on_a(
                        chain_ev.event,
                    ) {
                        self.src_queries.push(chain_query_consensus_state_request(
                            self.event.trigger_chain,
                            self.event.chain_height,
                            obj.client_id()?,
                            a.client_heights[&obj.client_id()?],
                            true,
                        ))
                    }
                    // query the builder object, e.g. connection, channel, etc
                    self.src_queries
                        .push(chain_query_object_request(&self.event, true)?);

                    // query object on destination chain if applicable (e.g. for connections
                    // and channels).
                    self.src_queries.push(chain_query_flipped_object_request(
                        self.dest_chain,
                        &self.event,
                        false,
                    )?);

                    new_state = BuilderState::QueryingObjects;
                    requests = BuilderRequests {
                        src_queries: self.src_queries.clone(),
                        dest_queries: self.dest_queries.clone(),
                        ..requests.clone()
                    };
                }

                Ok((new_state, requests))
            }
            _ => Err("event is ignored".into()),
        }
    }

    fn chain_from_client(&self, client_id: ClientId) -> Result<ChainId, BoxError> {
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
}

#[derive(Debug, Clone, Default)]
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
