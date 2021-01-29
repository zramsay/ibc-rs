--------------------------- MODULE ICS02 ----------------------------

EXTENDS Integers, FiniteSets, ICS02Definitions

\* max client identifier
CONSTANT MaxClientId
ASSUME MaxClientId > 0
\* max height which clients can reach
CONSTANT MaxHeight
ASSUME MaxHeight > 0


\* set of client data
VARIABLE clients
\* counter used to generate client identifiers
VARIABLE nextClientId

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
    /\ clients = AsClients({})
    /\ nextClientId = 1

CreateClient ==
    /\ nextClientId < MaxClientId
    /\ \E clientHeight \in Heights:
        /\ clients' = clients \union
                      {[clientId |-> nextClientId, height |-> clientHeight]}
        /\ nextClientId' = nextClientId + 1
 
\* UpdateClient ==
\*     \E clientId \in ClientIds:
\*         \E clientHeight \in Heights:

Next ==
    \/ CreateClient
    \* \/ UpdateClient
    \/ UNCHANGED <<nextClientId, clients>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOk ==
    /\ nextClientId \in ClientIds \union { MaxClientId + 1 }
    /\ clients \in Clients(ClientIds, Heights)

\* the client identifiers created are smaller than `nextClientId`
ClientIdsCreated ==
    \A client \in clients:
        client.clientId < nextClientId

=============================================================================
