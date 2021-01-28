------------------------------ MODULE IBCCore ------------------------------

(***************************************************************************
 This is the main module in the specification of the IBC core protocols. 
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCCoreDefinitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          MaxVersion, \* maximal connection version (we assume versions are integers) 
          GenerateClientDatagrams, \* toggle generation of client datagrams for the relayer 
          GenerateConnectionDatagrams \* toggle generation of connection datagrams for the relayer

VARIABLES chainAstore, \* chain store of ChainA
          chainBstore, \* chain store of ChainB
          incomingDatagramsChainA, \* set of (client, connection) datagrams incoming to ChainA
          incomingDatagramsChainB, \* set of (client, connection) datagrams incoming to ChainB
          relayerHeights, \* the client heights of the relayer
          outgoingDatagrams, \* sets of (client, connection) datagrams outgoing of the relayer
          historyChainA, \* history variables for ChainA
          historyChainB \* history variables for ChainB
          
vars == <<chainAstore, chainBstore, 
          incomingDatagramsChainA, incomingDatagramsChainB,
          relayerHeights,
          outgoingDatagrams,
          historyChainA, historyChainB>>
          
chainAvars == <<chainAstore, incomingDatagramsChainA, historyChainA>>
chainBvars == <<chainBstore, incomingDatagramsChainB, historyChainB>>
relayerVars == <<relayerHeights, outgoingDatagrams>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system                      
      

(***************************************************************************
 Instances of Relayer and Chain
 ***************************************************************************)

Relayer == INSTANCE ICS18Relayer
            WITH GenerateClientDatagrams <- GenerateClientDatagrams,
                 GenerateConnectionDatagrams <- GenerateConnectionDatagrams,
                 relayerHeights <- relayerHeights
                 
\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingDatagrams <- incomingDatagramsChainA,
               history <- historyChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingDatagrams <- incomingDatagramsChainB,
               history <- historyChainB

(***************************************************************************
 Component actions
 ***************************************************************************)

\* RelayerAction: either correct relayer takes a step, leaving the other 
\* variables unchanged 
RelayerAction ==
    \/ /\ Relayer!Next
       /\ UNCHANGED chainAvars
       /\ UNCHANGED chainBvars

\* ChainAction: either chain takes a step, leaving the other 
\* variables unchanged       
ChainAction ==
    \/ /\ ChainA!Next
       /\ UNCHANGED chainBvars
       /\ UNCHANGED relayerVars
    \/ /\ ChainB!Next  
       /\ UNCHANGED chainAvars
       /\ UNCHANGED relayerVars  

(***************************************************************************
 IBCCore Environment actions
 ***************************************************************************)
\* Submit datagrams from relayers to chains
SubmitDatagrams ==
    /\ incomingDatagramsChainA' = AsSetDatagrams(incomingDatagramsChainA \union outgoingDatagrams["chainA"])
    /\ incomingDatagramsChainB' = AsSetDatagrams(incomingDatagramsChainB \union outgoingDatagrams["chainB"])
    /\ outgoingDatagrams' = [chainID \in ChainIDs |-> AsSetDatagrams({})]
    /\ UNCHANGED <<chainAstore, chainBstore, relayerHeights>>
    /\ UNCHANGED <<historyChainA, historyChainB>>
    
(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
Init ==
    /\ ChainA!Init
    /\ ChainB!Init
    /\ Relayer!Init
    
\* Next state action
Next ==
    \/ ChainAction
    \/ RelayerAction
    \/ SubmitDatagrams
    \/ UNCHANGED vars
    
   
\* Fairness constraint
Fairness ==
    /\ WF_vars(SubmitDatagrams)  
    /\ ChainA!Fairness
    /\ ChainB!Fairness
    /\ Relayer!Fairness

\* Specification formula
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************
 Invariants
 ***************************************************************************)

\* Type invariant
TypeOK ==
    /\ ChainA!TypeOK
    /\ ChainB!TypeOK
    /\ Relayer!TypeOK

(***************************************************************************
 Helper operators used in properties
 ***************************************************************************)
\* get chain store by ID
GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
        
\* returns true if there is a "ClientUpdate" datagram
\* in the incoming datagrams for chainID           
IsClientUpdateInIncomingDatagrams(chainID, h) ==
    LET clID == GetCounterpartyClientID(chainID) IN
    IF chainID = "chainA"
    THEN [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
            \in incomingDatagramsChainA
    ELSE [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
            \in incomingDatagramsChainB
   
\* returns true if there is a "ClientUpdate" datagram
\* in the outgoing datagrams for chainID             
IsClientUpdateInOutgoingDatagrams(chainID, h) ==
    LET clID == GetCounterpartyClientID(chainID) IN
    [type |-> "ClientUpdate", clientID |-> clID, height |-> h] 
        \in outgoingDatagrams[chainID]            
            
\* returns true if there is a "ConnOpenInit" datagram 
\* in outgoing datagrams for chainID
IsConnOpenInitInOutgoingDatagrams(chainID) ==
    LET clID == GetClientID(chainID) IN
    LET counterpartyClID == GetCounterpartyClientID(chainID) IN 
    LET connID == GetConnectionID(chainID) IN
    LET counterpartyConnID == GetCounterpartyConnectionID(chainID) IN
    
    [type |-> "ConnOpenInit", 
     connectionID |-> connID, 
     clientID |-> clID,
     counterpartyConnectionID |-> counterpartyConnID,
     counterpartyClientID |-> counterpartyClID] \in outgoingDatagrams[chainID]
            
----------------------------------------------------------------------------
(***************************************************************************
 Invariants & Properties
 ***************************************************************************)
(***************************************************************************
 Invariants: connection datagrams
 ***************************************************************************)    
\* once connInit is set to TRUE in the history variable, 
\* the connection never goes to UNINIT         
ConnectionInitInv ==
    /\ historyChainA.connInit => ~IsConnectionUninit(GetChainByID("chainA"))
    /\ historyChainB.connInit => ~IsConnectionUninit(GetChainByID("chainB"))

\* once connTryOpen is set to TRUE in the history variable, 
\* the connection never goes to UNINIT         
ConnectionTryOpenInv ==
    /\ historyChainA.connTryOpen => ~IsConnectionUninit(GetChainByID("chainA"))
    /\ historyChainB.connTryOpen => ~IsConnectionUninit(GetChainByID("chainB"))

\* once connOpen is set to TRUE in the history variable, 
\* the connection never goes to UNINIT, INIT, or TRYOPEN         
ConnectionOpenInv ==
    /\ historyChainA.connOpen => (/\ ~IsConnectionUninit(GetChainByID("chainA"))
                                  /\ ~IsConnectionInit(GetChainByID("chainA"))
                                  /\ ~IsConnectionTryOpen(GetChainByID("chainA")))
    /\ historyChainB.connOpen => (/\ ~IsConnectionUninit(GetChainByID("chainB"))
                                  /\ ~IsConnectionInit(GetChainByID("chainB"))
                                  /\ ~IsConnectionTryOpen(GetChainByID("chainB")))
                                  
(***************************************************************************
 Invariant [IBCInv]
 ***************************************************************************)
\* IBCInv invariant: conjunction of invariants  
IBCInv == 
    /\ GenerateConnectionDatagrams
         => /\ ConnectionInitInv
            /\ ConnectionTryOpenInv
            /\ ConnectionOpenInv 
    
(***************************************************************************
 Safety: client datagrams
 ***************************************************************************)    

\* it ALWAYS holds that, for every chainID and every height h:
\*  - if 
\*    * there is a "ClientUpdate" datagram for chainID and height h and 
\*    * the height h is smaller than the maximal counterparty client height 
\*      at chainID
\*  - then 
\*    * the height h is NEVER added to the counterparty client heights 
\* 
\* Note: this property does not hold when it is allowed to install older headers
ClientUpdateSafety ==
    [](\A chainID \in ChainIDs : \A h \in Heights : 
       (/\ IsClientUpdateInIncomingDatagrams(chainID, h)
        /\ h < GetMaxCounterpartyClientHeight(GetChainByID(chainID)))
        => [](~IsCounterpartyClientHeightOnChain(GetChainByID(chainID), h)))

(***************************************************************************
 Safety: connection datagrams
 ***************************************************************************)    

\* it ALWAYS holds that, for every chainID
\*  - if 
\*    * the connection end is in INIT
\*  - then 
\*    * it NEVER goes to UNINIT 
ConnectionInitSafety ==
    [](\A chainID \in ChainIDs:
        /\ IsConnectionInit(GetChainByID(chainID))
        => [](~IsConnectionUninit(GetChainByID(chainID))))

\* it ALWAYS holds that, for every chainID
\*  - if 
\*    * the connection end is in TRYOPEN
\*  - then 
\*    * it NEVER goes to UNINIT ]
ConnectionTryOpenSafety ==
    [](\A chainID \in ChainIDs:
        /\ IsConnectionTryOpen(GetChainByID(chainID))
        => [](~IsConnectionUninit(GetChainByID(chainID))))

\* it ALWAYS holds that, for every chainID
\*  - if 
\*    * the connection end is in OPEN
\*  - then 
\*    * it NEVER goes to UNINIT, INIT, or TRYOPEN              
ConnectionOpenSafety ==     
    [](\A chainID \in ChainIDs:
        /\ IsConnectionOpen(GetChainByID(chainID))
        => [](/\ ~IsConnectionUninit(GetChainByID(chainID))
              /\ ~IsConnectionInit(GetChainByID(chainID))
              /\ ~IsConnectionTryOpen(GetChainByID(chainID))))

(***************************************************************************
 Safety [IBCSafety]:
    Bad datagrams are not used to update the chain stores 
 ***************************************************************************)
\* IBCSafety property: conjunction of safety properties 
IBCSafety ==
    \* at least one relayer creates client datagrams
    /\ GenerateClientDatagrams
         => ClientUpdateSafety  
    \* at least one relayer creates connection datagrams
    /\ GenerateConnectionDatagrams
         => /\ ConnectionInitSafety
            /\ ConnectionTryOpenSafety
            /\ ConnectionOpenSafety 

(***************************************************************************
 Liveness: Eventual delivery of client datagrams
 ***************************************************************************)
 
\* it ALWAYS holds that, for every chainID:
\*  - if 
\*      * the counterparty client is not initialized
\*  - then
\*      * the chain EVENTUALLY creates the counterparty client
CreateClientDelivery == 
    [](\A chainID \in ChainIDs : 
        (GetCounterpartyClientHeights(GetChainByID(chainID)) = {})
        => <>(IsCounterpartyClientOnChain(GetChainByID(chainID))))

\* it ALWAYS holds that, for every chainID and every height h
\*  - if 
\*      * EVENTUALLY a ClientUpdate for height h is sent to chainID
\*  -  then 
\*      * EVENTUALLY height h is added to counterparty client heights of chainID
ClientUpdateDelivery ==
    [](\A chainID \in ChainIDs : \A h \in Heights :
       (<>IsClientUpdateInOutgoingDatagrams(chainID, h)   
            => <>(IsCounterpartyClientHeightOnChain(GetChainByID(chainID), h))))
 
(***************************************************************************
 Liveness: Eventual delivery of connection datagrams
 ***************************************************************************)
 
\* it ALWAYS holds that, for every chainID
\*  - if 
\*      * EVENTUALLY a ConnOpenInit is sent to chainID
\*  -  then 
\*      * EVENTUALLY the connections at chainID and its counterparty are open 
ConnOpenInitDelivery ==
    [](\A chainID \in ChainIDs : 
       (<>IsConnOpenInitInOutgoingDatagrams(chainID) 
          => <>(/\ IsConnectionOpen(GetChainByID(chainID))
                /\ IsConnectionOpen(GetChainByID(GetCounterpartyChainID(chainID))))))   
         
(***************************************************************************
 Liveness [IBCDelivery]: 
    If ChainA sends a datagram to ChainB, then ChainB eventually receives 
    the datagram
                   
 * ChainA sends a datagram iff a correct relayer constructs the datagram by 
   scanning ChainA's store
 * ChainB receives a datagram iff it acts upon this datagram
 ***************************************************************************)            
\* IBCDelivery property: conjunction of delivery properties 
IBCDelivery ==
    \* at least one relayer creates client datagrams
    /\ GenerateClientDatagrams
         => /\ CreateClientDelivery
            /\ ClientUpdateDelivery
    \* at least one relayer creates connection datagrams
    /\ GenerateConnectionDatagrams
         => ConnOpenInitDelivery 
               
=============================================================================
\* Modification History
\* Last modified Tue Dec 01 10:32:04 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:48:22 CET 2020 by ilinastoilkovska
