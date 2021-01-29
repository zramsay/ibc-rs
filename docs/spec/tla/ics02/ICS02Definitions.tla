------------------------ MODULE ICS02Definitions -------------------------

EXTENDS Integers, FiniteSets

\* set of all datagrams
\* Datagrams(ClientIds) == 

\* set of all client data
ClientData(ClientIds, Heights) == [
    clientId: ClientIds,
    height: Heights
]
Clients(ClientIds, Heights) == SUBSET ClientData(ClientIds, Heights)

=============================================================================