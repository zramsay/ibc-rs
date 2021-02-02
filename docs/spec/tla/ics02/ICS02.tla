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
\* if a client has a null height then the client does not exist
NullHeight == 0
\* set of possible outcomes
Outcomes == {"Null", "CreateOK", "UpdateOK", "UpdateClientNotFound", "UpdateHeightVerificationFailure", "ModelError"}

\* check if a client exists
ClientExists(clientId) ==
    clients[clientId] /= NullHeight

SetClientHeight(clientId, clientHeight) ==
    [clients EXCEPT ![clientId] = clientHeight]

CreateClient(clientHeight) ==
    \* check if the client exists (it shouldn't)
    IF ClientExists(nextClientId) THEN
        \* if the client to be created already exists,
        \* then there's an error in the model
        /\ outcome' = "ModelError"
        /\ UNCHANGED <<clients, nextClientId>>
    ELSE
        \* set the new client's height to `clientHeight`
        /\ clients' = SetClientHeight(nextClientId, clientHeight)
        \* update `nextClientId`
        /\ nextClientId' = nextClientId + 1
        \* set `outcome`
        /\ outcome' = "CreateOK"

CreateClientNext ==
    \* only create client if the model constant `MaxClientId` allows it
    /\ nextClientId < MaxClientId
    \* select a height for the client to be created at
    /\ \E clientHeight \in Heights:
        CreateClient(clientHeight)

UpdateClient(clientId, clientHeight) ==
    \* check if the client exists
    IF ClientExists(clientId) THEN
        \* if the client exists, check its height
        IF clients[clientId] < clientHeight THEN
            \* if its height is lower than the one being updated to
            \* then, update the client
            /\ clients' = SetClientHeight(clientId, clientHeight)
            \* set `outcome`
            /\ outcome' = "UpdateOK"
            /\ UNCHANGED <<nextClientId>>
        ELSE
            /\ outcome' = "UpdateHeightVerificationFailure"
            /\ UNCHANGED <<clients, nextClientId>>
    ELSE
        \* if the client does not exist, then return an error
        /\ outcome' = "UpdateClientNotFound"
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
    /\ clients = [ clientId \in ClientIds |-> NullHeight ]
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
    \* /\ clients \in Clients(ClientIds, Heights)
    /\ outcome \in Outcomes

\* the model never erros
ModelNeverErrors ==
    outcome /= "ModelError"

=============================================================================
