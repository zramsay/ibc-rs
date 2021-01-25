use ibc::ics24_host::identifier::ChainId;

use relayer::chain::handle::ChainHandle;
use relayer::chain::runtime::ChainRuntime;
use relayer::chain::CosmosSDKChain;
use relayer::config::Config;

use eyre::Report;

use std::collections::HashMap;

pub struct ChainHandles {
    handles: HashMap<ChainId, Box<dyn ChainHandle>>,
}

impl ChainHandles {
    pub fn new(config: Config) -> Result<Self, Report> {
        let mut handles = HashMap::new();
        for chain_config in config.chains {
            let chain_id = chain_config.id.clone();
            let (chain, _) = ChainRuntime::<CosmosSDKChain>::spawn(chain_config)?;
            println!("chain id: {:?}", chain_id);
            let result = handles.insert(chain_id, chain);
            assert!(result.is_none(), "handle should not exist");
        }
        Ok(Self { handles })
    }

    pub fn ids(&self) -> impl Iterator<Item = &ChainId> {
        self.handles.keys()
    }

    pub fn get(&self, id: &ChainId) -> Option<&Box<dyn ChainHandle>> {
        self.handles.get(id)
    }
}
