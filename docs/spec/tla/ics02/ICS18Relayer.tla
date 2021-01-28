--------------------------- MODULE ICS18Relayer ----------------------------

(***************************************************************************
 This module contains the specification of a relayer, which is an off-chain 
 process running a relayer algorithm 
 ***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, IBCCoreDefinitions

CONSTANTS GenerateClientDatagrams \* toggle generation of client datagrams

ASSUME /\ GenerateClientDatagrams \in BOOLEAN 

CONSTANTS MaxHeight \* set of possible heights of the chains in the system
          
VARIABLES chainAstore, \* store of ChainA
          chainBstore, \* store of ChainB
          outgoingDatagrams, \* a function that assigns a set of pending datagrams 
                             \* outgoing from the relayer to each chainID
          relayerHeights \* a function that assigns a height to each chainID
          
vars == <<chainAstore, chainBstore, outgoingDatagrams, relayerHeights>>
Heights == 1..MaxHeight \* set of possible heights of the chains in the system                     

GetChainByID(chainID) ==
    IF chainID = "chainA"
    THEN chainAstore
    ELSE chainBstore
 
(***************************************************************************
 Client datagrams
 ***************************************************************************)
\* Compute client datagrams designated for dstChainID. 
\* These are used to update the client for srcChainID on dstChainID.
\* Some client updates might trigger an update of the height that 
\* the relayer stores for srcChainID
ClientDatagrams(srcChainID, dstChainID, relayer) ==
    LET srcChain == GetChainByID(srcChainID) IN
    LET dstChain == GetChainByID(dstChainID) IN
    LET srcChainHeight == GetLatestHeight(srcChain) IN    
    LET srcClientHeight == GetMaxCounterpartyClientHeight(dstChain) IN
    LET srcClientID == GetClientID(srcChainID) IN

    LET emptySetDatagrams == AsSetDatagrams({}) IN

    \* check if the relayer chain height for srcChainID should be updated
    LET srcRelayerChainHeight == 
        IF relayer[srcChainID] < srcChainHeight
        THEN srcChainHeight
        ELSE relayer[srcChainID] IN 
        
    \* create an updated relayer    
    LET updatedRelayer ==
        [relayer EXCEPT ![srcChainID] = srcRelayerChainHeight] IN    
    
    \* generate datagrams for dstChainID
    LET dstDatagrams == 
        IF srcClientHeight = AsInt(nullHeight)
        THEN \* the src client does not exist on dstChainID 
             {AsDatagram([
                type |-> "ClientCreate", 
                height |-> srcChainHeight,
                clientID |-> srcClientID
             ])}
        ELSE \* the src client exists on dstChainID
            IF srcClientHeight < srcChainHeight
            THEN \* the height of the src client on dstChainID is smaller than the height of the src chain
                 {AsDatagram([
                   type |-> "ClientUpdate",
                   height |-> srcChainHeight,
                   clientID |-> srcClientID
                 ])}
            ELSE emptySetDatagrams IN                   
                    
    [datagrams|-> dstDatagrams, relayerUpdate |-> updatedRelayer]    
   
(***************************************************************************
 Compute client (from srcChainID to dstChainID)
 ***************************************************************************)
\* Currently supporting:
\*  -  ICS 02: Client updates
ComputeDatagrams(srcChainID, dstChainID) ==
    \* ICS 02 : Clients
    \* - Determine if light clients needs to be updated 
    IF GenerateClientDatagrams 
    THEN ClientDatagrams(srcChainID, dstChainID, relayerHeights) 
    ELSE [datagrams |-> AsSetDatagrams({}), relayerUpdate |-> relayerHeights]

(***************************************************************************
 Relayer actions
 ***************************************************************************)   
\* Update the height of the relayer client for some chainID
UpdateRelayerClientHeight(chainID) ==
    LET chainLatestHeight == GetLatestHeight(GetChainByID(chainID)) IN
    /\ relayerHeights[chainID] < chainLatestHeight
    /\ relayerHeights' = [relayerHeights EXCEPT 
                            ![chainID] = GetLatestHeight(GetChainByID(chainID))
                         ]
    /\ UNCHANGED <<chainAstore, chainBstore, outgoingDatagrams>>  

\* for two chains, srcChainID and dstChainID, where srcChainID /= dstChainID, 
\* create the pending datagrams and update the corresponding sets of pending datagrams
Relay(srcChainID, dstChainID) ==
    LET datagramsAndRelayerUpdate == ComputeDatagrams(srcChainID, dstChainID) IN
    /\ srcChainID /= dstChainID
    /\ outgoingDatagrams' = 
            [outgoingDatagrams EXCEPT 
                ![dstChainID] = AsSetDatagrams(outgoingDatagrams[dstChainID] 
                                \union 
                                datagramsAndRelayerUpdate.datagrams)
            ]
    /\ relayerHeights' = datagramsAndRelayerUpdate.relayerUpdate       
    /\ UNCHANGED <<chainAstore, chainBstore>>
    

\* update the relayer client heights
UpdateClient ==
    \E chainID \in ChainIDs : UpdateRelayerClientHeight(chainID)
    
\* create client datagrams    
CreateDatagrams ==
    \E srcChainID \in ChainIDs : \E dstChainID \in ChainIDs : 
        /\ Relay(srcChainID, dstChainID)

(***************************************************************************
 Specification
 ***************************************************************************)
\* Initial state predicate
\*    Initially:
\*        - the relayer heights are uninitialized (i.e., their height is nullHeight)
\*        - there are no datagrams
Init == 
    /\ relayerHeights = [chainID \in ChainIDs |-> AsInt(nullHeight)]
    /\ outgoingDatagrams = [chainID \in ChainIDs |-> AsSetDatagrams({})]
    
\* Next state action
\*    The relayer either:
\*        - updates its clients, or
\*        - creates datagrams, or 
\*        - does nothing
Next ==
    \/ UpdateClient
    \/ CreateDatagrams
    \/ UNCHANGED vars    
       
\* Fairness constraints
Fairness ==
    /\ \A chainID \in ChainIDs : 
            WF_vars(UpdateRelayerClientHeight(chainID))
    /\ \A srcChainID \in ChainIDs : \A dstChainID \in ChainIDs : 
            WF_vars(Relay(srcChainID, dstChainID))
               
(***************************************************************************
 Invariants
 ***************************************************************************)
\* Type invariant
TypeOK ==
    /\ relayerHeights \in [ChainIDs -> Heights \union {nullHeight}]
    /\ outgoingDatagrams \in [ChainIDs -> SUBSET Datagrams(MaxHeight)]

=============================================================================
\* Modification History
\* Last modified Tue Dec 01 10:50:40 CET 2020 by ilinastoilkovska
\* Created Fri Mar 06 09:23:12 CET 2020 by ilinastoilkovska
