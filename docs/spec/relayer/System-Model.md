# IBC 

The interblockchain communication protocol(IBC) is an end-to-end, connection-oriented, stateful
protocol for reliable, ordered, and authenticated communication between modules on separate distributed
ledgers. 

# System model

We assume the following roles in the IBC protocol:

- module
- full node
- light client node
- relayer. 

## Module

Module is a deterministic state machine whose operation (state transitions) is driven only by executing
input requests (IO and non-deterministic actions are not allowed). Requests are also called transactions, 
datagrams or messages. A module is typically part of the blockchain application (for example SDK module in Cosmos SDK
application) but could also be a standalone process. 

A module interacts with the external world by writing external facing data (as part of request processing) to a 
publicly available data store. To avoid module impersonation, data must be authenticated. This is typically ensured
by relying on asymmetric cryptography, where data is signed by the private key(s) and verified using the corresponding
public keys. In case of the blockchain based modules, blocks added to the blockchain are signed, and they typically 
contain the hash of the application state; with standalone modules, hash of the application state is directly signed.

To support authenticating part of the module state (for efficiency reasons), application state is typically written in
a Merkleised data store where data is organised using Merkle trees (see https://en.wikipedia.org/wiki/Merkle_tree) such
that data are stored in the leaf nodes, and inner nodes contain hashes of its children. Merkle tree based data store 
allows proving presence or absence of data at the given path of the tree by computing a number of hashes proportional 
to the logarithm of the number of leaf nodes of the tree. Therefore, in order to prove that some data *d* is present 
or absent in the module state, we need to provide:

- *root app hash* signed by either single or multiple private keys (depending whether it is a blockchain or a 
standalone module) 
- *path* in the tree where *d* is stored (or not for the proof of absence) and 
- *membership proof*, a set of hashes from the leaf node where *d* is stored to the root of the tree.     

### Channel

The core of the IBC protocol is ensuring that modules can exchange messages (we call them IBC packets) in a 
reliable and authenticated way. The core abstraction that facilitates IBC packets exchange between modules is called 
channel. An IBC channel ensures the following properties:

**[Naming]**: Each channel between two modules A and B is uniquely identified. 

**[Authentication]**: If a module B receives a packet *p* from a module A at time *t*, then A has written *p* destined 
to B in its store before *t*. 

NOTE: When we refer to time in the previous definition, we assume existence of an external reference time 
(birds perspective) that allows us to logically define before relations between send/receive events. We don't talk 
about a particular distributed implementation.      

**[Eventual Delivery]**: If a module A writes a packet *p* destined to module B, then B will eventually receive and
process the packet *p*. Furthermore, the packet *p* is received exactly once by the module B. 

**[Eventual Acknowledgment]** If a module B receives a packet *p*, then A will eventually receive an acknowledgment
that was generated as part of processing of the packet *p*.

**[Timeout]**: If a module A writes a packet *p* to a channel *C* and the packet *p* is not received by the counterparty 
module B before defined timeout expires, then the packet is dropped and the corresponding timeout datagram is received by the 
module A. 

TODO: Introduce timeouts better. 
                              
IBC considers two kinds of channels, ordered and unordered channels. Ordered channels ensures that packets are received
in the order in which they are sent.

**[Total Order]**: If a module A writes a packet *p1* to an ordered channel before a packet *p2*, then if the module
B receives the packet *p2*, then the packet *p1* has already been received before. Furthermore, the module B receives
two packets *p1* and *p2* such that *p1* is received before *p2*, then the module A will eventually receive the 
corresponding acknowledgments in the same order, i.e., first the acknowledgment that is result of the reception of the
packet *p1* and then the acknowledgment from the *p2*.   

 
      
## Full node






Relayers are processes that provide connection layer of the IBC protocol. In the IBC protocol, on chain
modules do not have a way of directly sending a message to each other; this is the responsibility of relayer
processes. Modules signal its intention to send a message by writing data in its data store at the
defined location, and make those data (with corresponding proofs) available to external parties.
Relayer processes read (we say also scan) the state of each chain, construct appropriate IBC datagrams,
verify the corresponding proofs and submit valid datagrams to destination chain.   
We assume existence of multiple relayers, where some relayers could be faulty (behave arbitrarily),
but there is always at least a single correct relayer. We don't make assumptions on the maximum number of 
faulty relayers.

For the purpose of this specification we assume existence of two on chain modules A and B, that executes
IBC protocol. We say that a module A (or B) sends an IBC datagram m to a module B (or A) when a correct
relayer can construct valid datagram m by scanning the state of the chain A. We say that a module A receives
an IBC datagram m, when m was processed by the module A on chain. We assume that modules
are correct.    

Correct relayers need to ensure the following properties:

**[ICS18-Delivery]**: If a module A sends an IBC datagram m to a module B, then m is
eventually received by the module B.

**[ICS18-Validity]**: If a module B receives an IBC datagram m from a module A, 
then m was sent by the module A to the module B.

## System model

We assume that a correct relayer operates in the following model:

### Connected chains

Relayer transfers data between two chains: chainA and chainB. For simplicity, we assume Tendermint chains. 
Each chain operates under Tendermint security model:
- given a block b at height h committed at time `t = b.Header.Time`, `+2/3` of voting power behaves correctly
at least before `t + UNBONDING_PERIOD`, where `UNBONDING_PERIOD` is a system parameter (typically order of weeks).
Validators sets can be changed in every block, and we don't assume any constraint on the way validators are changed
(application specific logic).  

Furthermore, we assume that blockchain applications that operate on top of chainA and chainB writes
relevant data into Merkleised data store (for example IBC packets), and that parts of the store are publicly
available (so relayers can access it). 

In order to access IBC relevant data, a relayer needs to establish connections with full nodes (correct) from 
both chains. Note that there is no constrain on number of faulty full nodes: we can only assume that a correct relayer
will eventually have access to a correct full node. 

### Data availability

Note that data written to a store at height *h* as part of executing block *b* (`b.Height = h`) is effectively committed by 
the next block (at height h+1). The reason is the fact that the data store root hash as an effect of executing block at 
height h is part of the block header at height h+1. Therefore, data read at height h is available until time 
`t = b.Header.Time + UNBONDING_PERIOD`, where `b.Header.Height = h+1`. After time *t* we cannot trust that data anymore.
Note that data present in the store are re-validated by each new block: data added/modified at block *h* are still 
valid even if not altered after, as they are still "covered" by the root hash of the store. 

Therefore UNBONDING_PERIOD gives absolute time bound during which relayer needs to transfer data read at source chain
to the destination chain. As we will explain below, due to fork detection and accountability protocols, the effective 
data availability period will be shorter than UNBONDING_PERIOD. 

### Data verification

As connected chains in IBC do not blindly trust each other, data coming from the opposite chain must be verified at
the destination before being acted upon. Data verification in IBC is implemented by relying on the concept of light client.
Light client is a process that by relying on an initial trusted header (subjective initialisation), verifies and maintains 
set of trusted headers. Note that a light client does not maintain full blockchain and does not execute (verify) application
transitions. It operates by relying on the Tendermint security model, and by applying header verification logic that operates
only on signed headers (header + corresponding commit). 

More details about light client assumptions and protocols can be found 
[here](https://github.com/tendermint/spec/tree/master/rust-spec/lightclient). For the purpose of this document, we assume
that a relayer has access to the light client node that provides trusted headers.
Given a data d read at a given path at height h with a proof p, we assume existence of a function 
`VerifyMembership(header.AppHash, h, proof, path, d)` that returns `true` if data was committed by the corresponding
chain at height *h*. The trusted header is provided by the corresponding light client. 
