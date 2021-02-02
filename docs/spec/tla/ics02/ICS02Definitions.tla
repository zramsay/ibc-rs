------------------------ MODULE ICS02Definitions -------------------------

EXTENDS Integers, FiniteSets

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

ClientType == [
    clientId |-> Int,
    height |-> Int
]
AsClients(clients) == clients <: {ClientType}

\* set of all client data
ClientData(ClientIds, Heights) == [
    clientId: ClientIds,
    height: Heights
]
Clients(ClientIds, Heights) == [ClientIds -> Heights]
\* SUBSET ClientData(ClientIds, Heights)

=============================================================================