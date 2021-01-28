------------------------------ MODULE IBCCore ------------------------------

(***************************************************************************
 This is the main module in the specification of the IBC core protocols. 
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCCoreDefinitions

CONSTANTS MaxHeight, \* maximal height of all the chains in the system
          GenerateClientDatagrams \* toggle generation of client datagrams for the relayer 

VARIABLES chainAstore, \* chain store of ChainA
          chainBstore, \* chain store of ChainB
          incomingDatagramsChainA, \* set of client datagrams incoming to ChainA
          incomingDatagramsChainB, \* set of client datagrams incoming to ChainB
          relayerHeights, \* the client heights of the relayer
          outgoingDatagrams \* sets of client datagrams outgoing of the relayer
          
vars == <<chainAstore, chainBstore, 
          incomingDatagramsChainA, incomingDatagramsChainB,
          relayerHeights,
          outgoingDatagrams>>
          
chainAvars == <<chainAstore, incomingDatagramsChainA>>
chainBvars == <<chainBstore, incomingDatagramsChainB>>
relayerVars == <<relayerHeights, outgoingDatagrams>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system                      
      

(***************************************************************************
 Instances of Relayer and Chain
 ***************************************************************************)

Relayer == INSTANCE ICS18Relayer
            WITH relayerHeights <- relayerHeights,
                 outgoingDatagrams <- outgoingDatagrams
                 
\* We suppose there are two chains that communicate, ChainA and ChainB
\* ChainA -- Instance of Chain.tla
ChainA == INSTANCE Chain
          WITH ChainID <- "chainA",
               chainStore <- chainAstore,
               incomingDatagrams <- incomingDatagramsChainA

\* ChainB -- Instance of Chain.tla 
ChainB == INSTANCE Chain
          WITH ChainID <- "chainB",
               chainStore <- chainBstore,
               incomingDatagrams <- incomingDatagramsChainB

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
            
----------------------------------------------------------------------------
(***************************************************************************
 Properties
 ***************************************************************************)
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
 Safety [IBCSafety]:
    Bad datagrams are not used to update the chain stores 
 ***************************************************************************)
\* IBCSafety property: conjunction of safety properties 
IBCSafety ==
    \* at least one relayer creates client datagrams
    /\ GenerateClientDatagrams
         => ClientUpdateSafety  

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

=============================================================================
\* Modification History
\* Last modified Tue Dec 01 10:32:04 CET 2020 by ilinastoilkovska
\* Created Fri Jun 05 16:48:22 CET 2020 by ilinastoilkovska
