------------------------ MODULE IBCCoreDefinitions -------------------------

(***************************************************************************
 This module contains definitions of operators that are shared between the 
 different modules.
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* connection end type
ConnectionEndType == 
    [
        state |-> STRING, 
        connectionID |-> STRING, 
        clientID |-> STRING,
        counterpartyConnectionID |-> STRING, 
        counterpartyClientID |-> STRING,
        versions |-> {Int}
    ]


\* chain store type 
ChainStoreType == 
    [
        height |-> Int, 
        counterpartyClientHeights |-> {Int},
        connectionEnd |-> ConnectionEndType 
    ]

\* history variable type
HistoryType == 
    [
        connInit |-> BOOLEAN, 
        connTryOpen |-> BOOLEAN,
        connOpen |-> BOOLEAN
    ]

\* client datagram type
ClientDatagramType ==
    [
        type |-> STRING,
        clientID |-> STRING,
        height |-> Int   
    ]

\* connection datagram type
ConnectionDatagramType ==
    [
        type |-> STRING,
        connectionID |-> STRING,
        clientID |-> STRING,
        counterpartyConnectionID |-> STRING,
        counterpartyClientID |-> STRING,
        version |-> {Int},
        proofHeight |-> Int,
        consensusHeight |-> Int
    ]

\* datagram type (record type containing fields of all datagrams)                  
DatagramType ==
    [
        type |-> STRING,
        height |-> Int,
        proofHeight |-> Int,
        consensusHeight |-> Int,
        clientID |-> STRING,
        counterpartyClientID |-> STRING,
        connectionID |-> STRING,
        desiredConnectionID |-> STRING,
        counterpartyConnectionID |-> STRING,
        version |-> {Int}
    ]

AsID(ID) == ID <: STRING
AsInt(n) == n <: Int
AsSetInt(S) == S <: {Int}
AsString(s) == s <: STRING

AsConnectionEnd(connectionEnd) == connectionEnd <: ConnectionEndType  

AsChainStore(chainStore) == chainStore <: ChainStoreType

AsHistory(history) == history <: HistoryType

AsDatagram(dgr) == dgr <: DatagramType

AsClientDatagram(dgr) == dgr <: ClientDatagramType
AsSetClientDatagrams(Dgrs) == Dgrs <: {ClientDatagramType}

AsConnectionDatagram(dgr) == dgr <: ConnectionDatagramType
AsSetConnectionDatagrams(Dgrs) == Dgrs <: {ConnectionDatagramType}

AsSetDatagrams(Dgrs) == Dgrs <: {DatagramType}
AsSeqDatagrams(Dgrs) == Dgrs <: Seq(DatagramType)

(********************** Common operator definitions ***********************)
ChainIDs == {"chainA", "chainB"} 
ClientIDs == {"clA", "clB"}
ConnectionIDs == {"connAtoB", "connBtoA"}

nullHeight == 0
nullClientID == "none"
nullConnectionID == "none"

ConnectionStates == {"UNINIT", "INIT", "TRYOPEN", "OPEN"}

Max(S) == CHOOSE x \in S: \A y \in S: y <= x 
Min(S) == CHOOSE x \in S: \A y \in S: y >= x 

    
(***************************** ConnectionEnds *****************************
    A set of connection end records. 
    A connection end record contains the following fields:
    
    - state -- a string 
      Stores the current state of this connection end. It has one of the 
      following values: "UNINIT", "INIT", "TRYOPEN", "OPEN".
    
    - connectionID -- a connection identifier
      Stores the connection identifier of this connection end.
    
    - counterpartyConnectionID -- a connection identifier
      Stores the connection identifier of the counterparty connection end.
    
    - clientID -- a client identifier
      Stores the client identifier associated with this connection end. 
      
    - counterpartyClientID -- a client identifier
      Stores the counterparty client identifier associated with this connection end.

    - versions -- a set of versions
      Stores the set of supported connection versions. At the end of a handshake, 
      it should be a singleton set.
 ***************************************************************************)
ConnectionEnds(maxVersion) ==
    LET versions == 1..maxVersion IN
    [
        state : ConnectionStates,
        connectionID : ConnectionIDs \union {nullConnectionID},
        counterpartyConnectionID : ConnectionIDs \union {nullConnectionID},
        clientID : ClientIDs \union {nullClientID},
        counterpartyClientID : ClientIDs \union {nullClientID},
        versions : SUBSET versions
    ] <: {ConnectionEndType} 
    
(******************************** ChainStores ******************************
    A set of chain records. 
    A chain record contains the following fields:
    
    - height : an integer between nullHeight and MaxHeight. 
      Stores the current height of the chain.
    
    - counterpartyClientHeights : a set of integers between 1 and MaxHeight
      Stores the heights of the client for the counterparty chain.

    - connectionEnd : a connection end record 
      Stores data about the connection with the counterparty chain
 ***************************************************************************)
ChainStores(maxHeight, maxVersion) ==    
    [
        height : 1..maxHeight,
        counterpartyClientHeights : SUBSET(1..maxHeight),
        connectionEnd : ConnectionEnds(maxVersion)
    ] <: {ChainStoreType}

(******************************** Datagrams ********************************
 A set of datagrams.
 ***************************************************************************)
Datagrams(maxHeight, maxVersion) ==
    LET versions == 1..maxVersion IN
    [
        type : {"ClientCreate"}, 
        clientID : ClientIDs, 
        height : 1..maxHeight
    ] \union [
        type : {"ClientUpdate"}, 
        clientID : ClientIDs, 
        height : 1..maxHeight
    ] \union [
        type : {"ConnOpenInit"}, 
        connectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs
    ] \union [
        type : {"ConnOpenTry"}, 
        desiredConnectionID : ConnectionIDs, 
        counterpartyConnectionID : ConnectionIDs, 
        clientID : ClientIDs, 
        counterpartyClientID : ClientIDs, 
        versions : SUBSET versions,
        proofHeight : 1..maxHeight, 
        \* TODO: if the consensusHeight is 0, it means that the connOpenTry happened before the client behind created
        \*       this is likely not allowed by the ICS
        \*       - I'm allowing the consensusHeight to be 0 here just for the TypeOK invariant to hold
        consensusHeight : 0..maxHeight
    ] \union [
        type : {"ConnOpenAck"}, 
        connectionID : ConnectionIDs, 
        proofHeight : 1..maxHeight, 
        consensusHeight : 1..maxHeight 
    ] \union [
        type : {"ConnOpenConfirm"}, 
        connectionID : ConnectionIDs, 
        proofHeight : 1..maxHeight
    ]
    <: {DatagramType}
    
NullDatagram == 
    [type |-> "null"] <: DatagramType    
    
Histories ==
    [
        connInit : BOOLEAN,
        connTryOpen : BOOLEAN, 
        connOpen : BOOLEAN
     ] 
     <: {HistoryType}

\* Initial value of a connection end:
\*      - state is "UNINIT"
\*      - connectionID, counterpartyConnectionID are uninitialized
\*      - clientID, counterpartyClientID are uninitialized  
\*      - versions is an arbitrary subset of the set {1, .., maxVersion}   
InitConnectionEnds(maxVersion) ==
    LET versions == 1..maxVersion IN
    [
        state : {"UNINIT"},
        connectionID : {nullConnectionID},
        clientID : {nullClientID},
        counterpartyConnectionID : {nullConnectionID},
        counterpartyClientID : {nullClientID},
        versions : (SUBSET versions) \ {{}}
    ]

\* Initial value of the chain store: 
\*      - height is initialized to 1
\*      - the counterparty light client is uninitialized
\*      - the connection end is initialized to InitConnectionEnd 
InitChainStore(maxVersion) == 
    [
        height : {1},
        counterpartyClientHeights : {AsSetInt({})}, 
        connectionEnd : InitConnectionEnds(maxVersion)
    ] 
    <: {ChainStoreType}
        

\* Initial value of history flags         
InitHistory ==
     [
        connInit |-> FALSE,
        connTryOpen |-> FALSE,
        connOpen |-> FALSE
     ]  <: HistoryType  
         
(***************************************************************************
 Client helper operators
 ***************************************************************************)

\* get the ID of chainID's counterparty chain    
GetCounterpartyChainID(chainID) ==
    IF chainID = "chainA" THEN AsID("chainB") ELSE AsID("chainA")    
 
\* get the client ID of the client for chainID 
GetClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clA") ELSE AsID("clB")
        
\* get the client ID of the client for chainID's counterparty chain           
GetCounterpartyClientID(chainID) ==
    IF chainID = "chainA" THEN AsID("clB") ELSE AsID("clA")
    
\* get the latest height of chainID
GetLatestHeight(chain) ==
    AsInt(chain.height)   
      
\* get the maximal height of the client for chainID's counterparty chain    
GetMaxCounterpartyClientHeight(chain) ==
    IF chain.counterpartyClientHeights /= AsSetInt({})
    THEN AsInt(Max(chain.counterpartyClientHeights))
    ELSE AsInt(nullHeight)

\* get the set of heights of the client for chainID's counterparty chain    
GetCounterpartyClientHeights(chain) ==
    AsSetInt(chain.counterpartyClientHeights)        

\* returns true if the counterparty client is initialized on chainID
IsCounterpartyClientOnChain(chain) ==
    AsInt(chain.counterpartyClientHeights) /= AsInt({})

\* returns true if the height h is in counterparty client heights on chainID 
IsCounterpartyClientHeightOnChain(chain, h) ==
    h \in chain.counterpartyClientHeights
     
(***************************************************************************
 Connection helper operators
 ***************************************************************************)

\* get the connection ID of the connection end at chainID
GetConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("connAtoB")
    ELSE IF chainID = "chainB"
         THEN AsID("connBtoA")
         ELSE AsID(nullConnectionID)      

\* get the connection ID of the connection end at chainID's counterparty chain
GetCounterpartyConnectionID(chainID) ==
    IF chainID = "chainA"
    THEN AsID("connBtoA")
    ELSE IF chainID = "chainB"
         THEN AsID("connAtoB")
         ELSE AsID(nullConnectionID)
          
\* get the connection end at chainID
GetConnectionEnd(chain) == 
    AsConnectionEnd(chain.connectionEnd)
    
\* pick the minimal version from a set of versions
PickVersion(versions) == 
    IF versions /= AsSetInt({})
    THEN LET minVersion == Min(versions) IN
         {minVersion}
    ELSE AsSetInt({})
    

\* returns true if the connection end on chainID is UNINIT
IsConnectionUninit(chain) ==
    AsString(chain.connectionEnd.state) = "UNINIT"

\* returns true if the connection end on chainID is INIT
IsConnectionInit(chain) ==
    chain.connectionEnd.state = "INIT"

\* returns true if the connection end on chainID is TRYOPEN
IsConnectionTryOpen(chain) ==
    chain.connectionEnd.state = "TRYOPEN"
    
\* returns true if the connection end on chainID is OPEN
IsConnectionOpen(chain) ==
    chain.connectionEnd.state = "OPEN"
          
=============================================================================
\* Modification History
\* Last modified Tue Dec 01 10:41:22 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:56:21 CET 2020 by ilinastoilkovska