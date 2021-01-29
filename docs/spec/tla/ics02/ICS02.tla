--------------------------- MODULE ICS02 ----------------------------

EXTENDS Integers, FiniteSets, ICS02Definitions

\* max client identifier
CONSTANT MaxClientId
\* max height which clients can reach
CONSTANT MaxHeight


\* counter used to generate client identifiers
VARIABLE nextClientId
\* mapping from client identifier to its data
VARIABLE clientMap


\* set of possible client identifiers
ClientIds == 1..MaxClientId
\* set of possible heights
Heights == 1..MaxHeight

\* a datagram to create a client at a certain height
CreateClientDatagram ==
    \E height \in Heights:
        AsDatagram([
            type |-> "ClientCreate",
            height |-> height
        ])

\* a datagram to update client to a certain height
UpdateClientDatagram ==
    \E clientId \in ClientIds:
        \E height \in Heights:
            AsDatagram([
                type |-> "ClientUpdate",
                clientId |-> clientId,
                height |-> height
            ])

(***************************************************************************
 Specification
 ***************************************************************************)

 Init ==
    /\ nextClientId = 1
    /\ clientMap = AsClientMap({}, ClientIds)
    
Update ==
    /\ nextClientId <= MaxClientId
    /\ nextClientId' = nextClientId + 1
    /\ UNCHANGED <<clientMap>>

Next ==
    \/ Update
    \/ UNCHANGED <<nextClientId, clientMap>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ nextClientId \in 1..(MaxClientId + 1)
    /\ clientMap \in ClientMapType(ClientIds)

=============================================================================
