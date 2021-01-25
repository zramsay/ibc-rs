mod channels;
mod handles;

use channels::Channels;
use handles::ChainHandles;

use ibc::ics24_host::identifier::ChainId;

use eyre::{Report, WrapErr};

const CONFIG_FILE: &str = "loop_config.toml";
const CHAIN_ID_0: &str = "ibc-0";
const CHAIN_ID_1: &str = "ibc-1";
const CHAIN_ID_2: &str = "ibc-2";

fn main() -> Result<(), Report> {
    tracing_subscriber::fmt::init();

    let config = relayer::config::parse(CONFIG_FILE).wrap_err("parsing config")?;
    let handles = ChainHandles::new(config)?;

    let chain_id_0: ChainId = CHAIN_ID_0.parse().unwrap();
    let chain_id_1: ChainId = CHAIN_ID_1.parse().unwrap();
    let chain_id_2: ChainId = CHAIN_ID_2.parse().unwrap();
    // connect ibc-0 with ibc-1 and ibc-2 with ibc-2
    let chain_id_pairs = vec![(chain_id_0, chain_id_1.clone()), (chain_id_1, chain_id_2)];
    let channels = Channels::setup(chain_id_pairs, handles)?;

    Ok(())
}
