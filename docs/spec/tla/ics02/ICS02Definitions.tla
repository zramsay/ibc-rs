------------------------ MODULE ICS02Definitions -------------------------

EXTENDS Integers, FiniteSets

(********************* TYPE ANNOTATIONS FOR APALACHE ***********************)
\* operator for type annotations
a <: b == a

\* client datagram type
DatagramType == [
    type |-> STRING,
    clientId |-> STRING,
    height |-> Int   
]
AsDatagram(datagram) == datagram <: DatagramType

\* client data and client map types
ClientDataType == [
    height |-> Int
]
ClientMapType(ClientIds) == [
    ClientIds -> SUBSET ClientDataType
]
AsClientMap(clientMap, ClientIds) ==  clientMap <: ClientMapType(ClientIds)

=============================================================================