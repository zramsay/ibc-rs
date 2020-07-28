

// Chains that a relayer might talk to:
// 
// - LocalChain - just for testing. in-process. not ABCI based ... just an in-process state transition function
// 	- leverage the mbt tools Andrey has been building
// 
// Tendermint/ABCI chains - implementations of Chain are roughly identical, except for some chain specific "prefixes" and merkle proof types
// - ABCIRSFrameworkChain - utilize the same IBC "handlers" as the LocalChain, but in an ABCI app
// - CosmosSDKChain - cosmos sdk ... abci based
// - LotionJSChain - uses the lotion js abci framework 
// 
// - SubstrateChain - not abci based, substrate stuff ...
// 
// 

pub trait Chain {
	type Msg;

	// - abci_query() rpc endpoint for tendermint-based chains
	// - some equivalent for substrate chains
	// - just read direct from in-process state for local chain
	query_xxx(params);
	...

	broadcast_tx(msg: Msg);
}


// impl of the LocalChain broadcast_tx

impl Chain for LocalChain {
	pub fn broadcast_tx(msg: Self::Msg) {
		state_transition(Self::ibc_state, msg)	
	}
}

fn state_transition(st: IBCState, msg: MsgType) -> HashMap {

    match msg{
        MsgType::CreateClient(m) => ics07.create_client(st, m),
        MsgType::UpdateClient(m) => ics07.update_client(st, m),
        MsgType::ConnInit(m) => ics03.conn_init(st, m),
        ...
        _ => 

    }
}

pub struct IBCState {
	// expose get/set on the store
	// expose other helper functions eg. versions() ...

	// this needs to support atomic txs

	// would be cool if this was a collection of IBC objects (clients, connections, etc.)
	// and we could test them directly and delegate mutating a store to some other component
	// that could handle atomicity concerns etc.
}

// create a new Connection in INIT state and store it 
fn conn_init(st: IBCState, msg: MsgConnectionOpenInit) -> Result<IBCState, Error> {
    // validate the connection id (stateless)
    validateConnectionIdentifier(msg.connection_id)?;

    // check that connection id doesnt already exist in the store
    st.get(connectionPath(msg.connection_id)) == null)?;

    // -----------------

    let conn = ics03::ConnectionEnd::new(msg.client_id, msg.counterparty, st.versions())?;
    conn.set_state(ics03::State::Init);

    // -----------------

    // needs to happen atomically 
    st.set(connectionPath(msg.connection_id), conn)
    st.addConnectionToClient(msg.client_id, msg.connection_id)
}

// "runs on chainB"
fn conn_open_try(st: IBCState, msg: MsgConnectionOpenTry) -> Result<IBCState, Error>{
    validateConnectionIdentifier(msg.connection_id)?

    // check that chainA's client for chainB is below chainB's current height
    // TODO: is this redundant somewhere? can we remove it somehow?
    let consensus_height = msg.proof.consensus_proof.consensus_height 
    consensus_height < st.getCurrentHeight() ?

    let expected_conensus_state = st.getConsensusState(consensus_height)
    let expected_conn = ics03::ConnectionEnd::new(msg.client_id, msg.counterparty, msg.counterparty_versions)?;
    conn.set_state(ics03::State::Init);

    version = st.pickVersion(msg.counterparty_versions)

    ... 

}

