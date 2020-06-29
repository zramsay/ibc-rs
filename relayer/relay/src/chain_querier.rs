use crate::chain::tendermint::TendermintChain;
use crate::config::Config;
use crate::query::ibc_query;
use crate::relayer_state::{BuilderObject, BuilderTrigger};
use relayer_modules::query::{IbcQuery, IbcResponse};
use tokio::sync::mpsc::{Receiver, Sender};
use tracing::info;

// event_handler to Chain for queries
#[derive(Debug, Clone)]
pub struct ChainQueryRequest<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    pub trigger: BuilderTrigger<O>,
    pub request: Q,
}

#[derive(Debug, Clone)]
pub struct ChainQueryResponse<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    pub trigger: BuilderTrigger<O>,
    pub response: Q::Response,
}

fn matching_req_resp<O, Q>(req: &ChainQueryRequest<O, Q>, resp: &ChainQueryResponse<O, Q>) -> bool
where
    O: BuilderObject,
    Q: IbcQuery,
{
    if req.trigger != resp.trigger {
        return false;
    }
    // TODO - no idea how to match req with resp
    true
}

pub(crate) fn valid_query_response<O, Q>(
    response: &ChainQueryResponse<O, Q>,
    queries: &[ChainQueryRequest<O, Q>],
) -> bool
where
    O: BuilderObject,
    Q: IbcQuery,
{
    for req in queries {
        if !matching_req_resp(req, &response) {
            continue;
        }
        return true;
    }
    false
}

/// The Querier handles query requests from the event handler.
pub struct ChainQueryHandler<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    config: Config,
    /// Channel where query requests are received from relayer.
    query_request_rx: Receiver<ChainQueryRequest<O, Q>>,
    /// Channel where query responses are sent to the relayer.
    query_response_tx: Sender<ChainQueryResponse<O, Q>>,
}

impl<O, Q> ChainQueryHandler<O, Q>
where
    O: BuilderObject,
    Q: IbcQuery,
{
    /// Constructor for the Query Handler
    pub fn new(
        config: Config,
        query_request_rx: Receiver<ChainQueryRequest<O, Q>>,
        query_response_tx: Sender<ChainQueryResponse<O, Q>>,
    ) -> Self {
        ChainQueryHandler {
            config,
            query_request_rx,
            query_response_tx,
        }
    }

    ///Query Handler loop
    pub async fn run(&mut self) {
        info!("running IBC Querier Handler");

        loop {
            if let Some(query) = self.query_request_rx.recv().await {
                let response = ibc_query(
                    &TendermintChain::from_config(
                        self.config
                            .chains
                            .iter()
                            .find(|c| c.id == query.trigger.chain)
                            .unwrap()
                            .clone(),
                    )
                    .unwrap(),
                    query.request,
                )
                .await
                .unwrap();

                let _res = self
                    .query_response_tx
                    .send(ChainQueryResponse {
                        trigger: query.trigger,
                        response,
                    })
                    .await;
            }
        }
    }
}
