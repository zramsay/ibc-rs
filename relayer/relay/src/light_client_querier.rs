use crate::relayer_state::{BuilderObject, BuilderTrigger};
use ::tendermint::chain::Id as ChainId;
use relayer_modules::ics07_tendermint::header::Header;
use tendermint::block::Height;
use tokio::sync::mpsc::{Receiver, Sender};
use tracing::info;

// event_handler requests to Light Client
#[derive(Debug, Clone)]
pub struct LightClientQuery<O>
where
    O: BuilderObject,
{
    pub trigger: BuilderTrigger<O>,
    pub request: LightClientRequest,
}

#[derive(Debug, Clone)]
pub enum LightClientRequest {
    ConsensusStateUpdateRequest(ConsensusStateUpdateRequestParams),
}

#[derive(Debug, Clone)]
pub struct ConsensusStateUpdateRequestParams {
    chain: ChainId,
    cs_height: Height,
    last_cs_height: Height,
}

impl ConsensusStateUpdateRequestParams {
    pub(crate) fn new(chain: ChainId, cs_height: Height, last_cs_height: Height) -> Self {
        ConsensusStateUpdateRequestParams {
            chain,
            cs_height,
            last_cs_height,
        }
    }
}

#[derive(Debug, Clone)]
pub struct LightClientQuerierResponse<O>
where
    O: BuilderObject,
{
    // this will change
    chain: ChainId,
    trigger: BuilderTrigger<O>,
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

pub struct LightClientQueryHandler<O>
where
    O: BuilderObject,
{
    /// Channel where LC query requests are received from relayer.
    light_client_request_rx: Receiver<LightClientQuery<O>>,
    /// Channel where LC query responses are sent to the relayer.
    light_client_response_tx: Sender<LightClientQuerierResponse<O>>,
}

impl<O> LightClientQueryHandler<O>
where
    O: BuilderObject,
{
    /// Constructor for the Query Handler
    pub fn new(
        light_client_request_rx: Receiver<LightClientQuery<O>>,
        light_client_response_tx: Sender<LightClientQuerierResponse<O>>,
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
