--------------------------- MODULE ICS02 ----------------------------

EXTENDS Integers, FiniteSets, ICS02Definitions

\* max client identifier
CONSTANT MaxClientId
ASSUME MaxClientId > 0
\* max height which clients can reach
CONSTANT MaxHeight
ASSUME MaxHeight > 0


\* counter used to generate client identifiers
VARIABLE nextClientId
\* set of client data
VARIABLE clients

\* set of possible client identifiers
ClientIds == 1..MaxClientId
\* set of possible heights
Heights == 1..MaxHeight

\* a datagram to create a client at a certain height
CreateClientDatagram ==
    \E height \in Heights:
        [
            type |-> "ClientCreate",
            height |-> height
        ]

\* a datagram to update client to a certain height
UpdateClientDatagram ==
    \E clientId \in ClientIds:
        \E height \in Heights:
            [
                type |-> "ClientUpdate",
                clientId |-> clientId,
                height |-> height
            ]

(***************************************************************************
 Specification
 ***************************************************************************)

 Init ==
    /\ nextClientId = 1
    /\ clients = {}

Update ==
    /\ nextClientId <= MaxClientId
    /\ nextClientId' = nextClientId + 1
    /\ UNCHANGED <<clients>>

Next ==
    \/ Update
    \/ UNCHANGED <<nextClientId, clients>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ nextClientId \in ClientIds \union { MaxClientId + 1 }
    /\ clients \in Clients(ClientIds, Heights)

=============================================================================
