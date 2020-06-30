use ::tendermint::chain::Id as ChainId;
use relayer_modules::ics07_tendermint::header::Header;
use tendermint::block::Height;
use tokio::sync::mpsc::{Receiver, Sender};
use tracing::info;

// event_handler requests to Light Client
#[derive(Debug, Clone)]
pub struct LightClientQuery {
    pub chain: ChainId,
    pub request: LightClientRequest,
}

#[derive(Debug, Clone)]
pub enum LightClientRequest {
    ConsensusStateUpdateRequest(ConsensusStateUpdateRequestParams),
}

#[derive(Debug, Clone)]
pub struct ConsensusStateUpdateRequestParams {
    cs_height: Height,
    last_cs_height: Height,
}

impl ConsensusStateUpdateRequestParams {
    pub(crate) fn new(cs_height: Height, last_cs_height: Height) -> Self {
        ConsensusStateUpdateRequestParams {
            cs_height,
            last_cs_height,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LightClientQueryResponse {
    // this will change
    chain: ChainId,
    trigger: LightClientRequest,
    response: LightClientResponse,
}

#[derive(Debug, Clone)]
pub enum LightClientResponse {
    ConsensusStateUpdates(ConsensusStateUpdatesResponse),
}

#[derive(Debug, Clone)]
pub struct ConsensusStateUpdatesResponse {
    headers: Vec<Header>,
}

pub struct LightClientQueryHandler {
    /// Channel where LC query requests are received from relayer.
    light_client_request_rx: Receiver<LightClientQuery>,
    /// Channel where LC query responses are sent to the relayer.
    light_client_response_tx: Sender<LightClientQueryResponse>,
}

impl LightClientQueryHandler {
    /// Constructor for the Query Handler
    pub fn new(
        light_client_request_rx: Receiver<LightClientQuery>,
        light_client_response_tx: Sender<LightClientQueryResponse>,
    ) -> Self {
        LightClientQueryHandler {
            light_client_request_rx,
            light_client_response_tx,
        }
    }

    ///Query Handler loop
    pub async fn run(&mut self) {
        info!("running Light Client Handler Loop");

        loop {
            let query = self.light_client_request_rx.recv().await;
            info!("Light Client Querier received {:?}", query);
        }
    }
}
