# Relayer

Relayer is an off-chain process responsible for relaying data between
two chains running the IBC protocol. It can be seen as a "physical" connection
layer of the IBC (Inter Blockchain Communication) protocol. It operates by
scanning the state of each chain (more preciselly blockchain and application
state), constructing appropriate IBC datagrams (messages echanged as part
of IBC protocol), and submitting them (for execution) to destination chains
as defined by the protocol.

# Term definitions

# Sequential Definition of Relayer

## Informal specification of Relayer

Relayer is a process that relays IBC packets (datagram) between modules
(typically on chain modules) that implements IBC protocol. Chains that
implement the IBC protocol do not have means to directly exchange messages
(according to the IBC specification). They instead write IBC packets to
its data store (typically Merkleised store), and then those packets are
read and forwarded to the destination module by the relayer process(es).
As modules do not trust each other, IBC packets carry also the proof
that packets was indeed written to the module data store. To ensure that
forwarded packets are accepted by the destination module, relayer is supposed
to verify packets before forwarding. IBC protocol allow existence of
multiple relayers, i.e., relayer is not a dedicated central component,
that are concurrently forwarding packets.

## Sequential specification of Relayer

To simplify presentation and make understanding of the relayer easier,
we will present relayer as a process that connects two modules A and B.
Each module has a corresponding data store in which IBC packets are written.
We assume that a relayer has a way of reading/sendingIBC packets from/to a module.

Relayer has to satisfy the following properties:

#### **[R-FORWARD]**:
If a module A writes an IBC packet m destined to a module B to its data store,
a relayer should ensure that m is eventually received by a module B.

#### **[R-PROOF]**:
Relayer should forward only IBC packets with a valid proof.

# Distributed Specification of Relayer

# Relayer protocol

## Data structures

```typescript
type Counterparty struct {
	ClientID     string
	ConnectionID string
	Prefix       commitment.PrefixI
}
```

## IBC datagrams

### Connection Handshake datagrams

#### MsgConnectionOpenInit

The `MsgConnectionOpenInit` message is used to initialize a connection.

```typescript
type MsgConnectionOpenInit struct {
	ConnectionID string         // connAtoB
	ClientID     string         // clB
	Counterparty Counterparty   // {ClientID: clA, ConnectionID: connBtoA, Prefix: "B_store">
	Signer       sdk.AccAddress  // Q: Why we need this field?
}
```

#### MsgConnectionOpenTry

The `MsgConnectionOpenTry` defines the message sent by the relayer to try to open a connection.

```typescript
type MsgConnectionOpenTry struct {
     ConnectionID         string            // connBtoA
     ClientID             string            // clA
     Counterparty         Counterparty      // {ClientID: clB, ConnectionID: connAtoB, Prefix: "A_store">
     CounterpartyVersions []string
     ProofInit            commitment.ProofI // proof that connAtoB connection end is stored on Chain A
     ProofConsensus       commitment.ProofI // proof that chain A stored chain B's consensus state at ConsensusHeight
     ProofHeight          uint64            // hA, height of A at which relayer retrieved ProofInit
     ConsensusHeight      uint64            // hB
     Signer               sdk.AccAddress
}
```

#### MsgConnectionOpenAck

`MsgConnectionOpenAck` defines the message sent by the relayer to chain A to acknowledge the change
of connection state to `TRYOPEN` on Chain B.

```typescript
type MsgConnectionOpenAck struct {
     ConnectionID    string            // connAtoB
     ProofTry        commitment.ProofI // proof that connBtoA on Chain B is in TRYOPEN state
     ProofConsensus  commitment.ProofI // proof that chain B stored chain A's consensus at ConsensusHeight
     ProofHeight     uint64            // hB, height of B at which relayer retrieved the ProofTry
     ConsensusHeight uint64            // hA, height of A in ProofConsensus
     Version         string
     Signer          sdk.AccAddress
}
```

#### MsgConnectionOpenConfirm

`MsgConnectionOpenConfirm` defines the message sent by the relayer to chain B to confirm the opening of a connection on chain A.

```typescript
type MsgConnectionOpenConfirm struct {
	ConnectionID string            // connBtoA
	ProofConfirm commitment.ProofI // proof that connAtoB on chain A is in OPEN state
	ProofHeight  uint64            // hA, height of A at which relayer retrieved the ProofAck
	Signer       sdk.AccAddress
}
```

#### MsgUpdateClient

`MsgUpdateClient` defines a message to update an IBC client.

```typescript
type MsgUpdateClient struct {
	ClientID string
	Header   Header
	Signer   sdk.AccAddress
}

type Header struct {
	SignedHeader    // contains the commitment root
	ValidatorSet
}
```

### Remote Functions

```typescript
func QueryConnection(id string, height int64) (ConnectionResponse, error)
```
- Implementation remark
   - RPC to full node *addr*
- Expected precondition
  - none
- Expected postcondition
  - if *addr* is correct: Returns the corresponding connectionEnd
  - if *addr* is faulty: Returns arbitrary connectionEnd
- Error condition
   * if *addr* is correct: none. We assume communication is reliable and timely.
   * if *addr* is faulty: arbitrary error (including timeout).
----

```typescript
type ConnectionResponse struct {
	Connection  IdentifiedConnectionEnd
	Proof       MerkleProof
	ProofPath   MerklePath
	ProofHeight uint64
}

type IdentifiedConnectionEnd struct {
	Connection ConnectionEnd
	Identifier string
}
```

```typescript
func QueryClientState(id string, height int64) (ClientStateResponse, error)
```

```typescript
type StateResponse struct {
	ClientState ClientState
	Proof       MerkleProof
	ProofPath   MerklePath
	ProofHeight uint64
}
```

TODO: What should be the type of ClientState?

```typescript
func QueryClientConsensusState() (ConsensusStateResponse, error)
```

```typescript
type ConsensusStateResponse struct {
	ConsensusState ConsensusState
	Proof          MerkleProof
	ProofPath      MerklePath
	ProofHeight    uint64
}
```

TODO: What should be the type of ConsensusState?
TODO: What are the parameters for this function? It seems that we are
interested in querying light client state at the given height (header.h-1)
for a given height. Most probably light client state has an entry for
each height and we are interested knowing the value for a given height.



## Relayer protocol

```typescript
func CreateConnectionStep(chA Chain, chB Chain) {
    shA, vsA = getLatestShAndVs(chA)
    shB, vsB = getLatestShAndVs(chB)

    // To be able to prove connection state at height h we need a root app hash that is
    // part of header at height h+1.

    connectionResponseA, errorA = QueryConnection(chA.ConnectionId, shA.Height-1) // what if this fails?
    connectionResponseB, errorB = QueryConnection(chB.ConnectionId, shA.Height-1)

    clientStateA, errorA = QueryClientState(chA.ClientId, shA.Height-1) // note that in the go code height is not provided in this case!
    clientStateB, errorB = QueryClientState(chB.ClientId, shB.Height-1)

    latestHeightA = getLatestHeight(chA)
    latestHeightB = getLatestHeight(chB)

    consensusStateA, errorA = QueryClientConsensusState(chA.ClientId, shA.Height - 1, latestHeightA)
    consensusStateB, errorA = QueryClientConsensusState(chB.ClientId, shB.Height - 1, latestHeightB)

    switch {
    	case connectionResponseA.Connection.Connection.State == connState.UNINITIALIZED &&
    	     connectionResponseB.Connection.Connection.State == connState.UNINITIALIZED:

    		 send MsgConnectionOpenInit(chA.ConnectionID,
                                        chA.ClientID,
                                        chB.ConnectionID,
                                        chB.ClientID,
                                        defaultChainPrefix,
                                        signer) to chA

        // Handshake has started on dst (1 stepdone), relay `connOpenTry` and `updateClient` on src
        case connectionResponseA.Connection.Connection.State == connState.UNINITIALIZED &&
             connectionResponseB.Connection.Connection.State == connState.INIT:

        	send MsgUpdateClient(chA.clientId, shB, chA.GetAddress()) to chA
        	send MsgConnectionTry(chA.ConnectionID,
                                  chA.ClientID,
                                  chB.ConnectionID,
                                  chB.ClientID,
                                  defaultChainPrefix,
                                  defaultIBCVersions,
                                  consensusStateB.Proof,
                                  consensusStateB.Proof,
                                  connectionResponseB.ProofHeight+1,
                                  latestConsensusHeightB,
                                  signer) to chA

















}
```

