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
\* string with the outcome of the last operation
VARIABLE outcome

\* set of possible client identifiers
ClientIds == 1..MaxClientId
\* set of possible heights
Heights == 1..MaxHeight
\* set of possible outcomes
Outcomes == {"Null", "CreateOK", "UpdateClientNotFound", "UpdateHeaderVerificationFailure", "ModelError"}

CreateClient(clientHeight) ==
    \* add a new client at height `clientHeight` with `nextClientId` as identifier
    /\ clients' = clients \union {[clientId |-> nextClientId, height |-> clientHeight]}
    \* update `nextClientId`
    /\ nextClientId' = nextClientId + 1
    \* update `outcome`
    /\ outcome' = "CreateOK"

CreateClientNext ==
    \* create client if the model constant `MaxClientId` allows it
    /\ nextClientId < MaxClientId
    \* select a height for the client to be created
    /\ \E clientHeight \in Heights:
        CreateClient(clientHeight)

UpdateClient(clientId, clientHeight) ==
    \* find the client to be updated
    LET find == {client \in clients : client.clientId = clientId} IN
    LET findCount == Cardinality(find) IN
    \* check if the client exists
    IF findCount = 0 THEN
        \* if the client does not exist, then return an error
        /\ outcome' = "UpdateClientNotFound"
        /\ UNCHANGED <<clients, nextClientId>>
    ELSE IF findCount = 1 THEN
        \* if the client exists, check its height
        CHOOSE client \in clients: TRUE
        /\ IF client.height < clientHeight THEN
            \* if its height is lower than the one being updated to
            \* then, update the client
            UNCHANGED <<outcome, clients, nextClientId>>
           ELSE
            UNCHANGED <<outcome, clients, nextClientId>>
    ELSE
        \* this case is not possible
        /\ outcome' = "ModelError"
        /\ UNCHANGED <<clients, nextClientId>>

UpdateClientNext ==
    \* select a client to be updated (which may not exist)
    \E clientId \in ClientIds:
        \* select a height for the client to be updated
        \E clientHeight \in Heights:
            UpdateClient(clientId, clientHeight)

(***************************************************************************
 Specification
 ***************************************************************************)

 Init ==
    /\ clients = AsClients({})
    /\ nextClientId = 1
    /\ outcome = "Null"

Next ==
    \/ CreateClientNext
    \/ UpdateClientNext
    \/ UNCHANGED <<clients, nextClientId, outcome>>

(***************************************************************************
 Invariants
 ***************************************************************************)

TypeOK ==
    /\ nextClientId \in ClientIds \union { MaxClientId + 1 }
    /\ clients \in Clients(ClientIds, Heights)
    /\ outcome \in Outcomes

\* the model never erros
ModelNeverErrors ==
    outcome /= "ModelError"

\* the client identifiers created are smaller than `nextClientId`
ClientIdsAllowed ==
    \A client \in clients:
        client.clientId < nextClientId

\* if two clients have the same identifier, then they are the same
ClientIdsUnique ==
    \A client1 \in clients:
        \A client2 \in clients:
            client1.clientId = client2.clientId => client1 = client2

=============================================================================
