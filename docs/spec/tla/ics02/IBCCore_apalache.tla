--------------------- MODULE IBCCore_apalache ---------------------

GenerateClientDatagrams == TRUE
MaxHeight == 5

\* the variables declared in IBCCore
VARIABLES chainAstore,
          chainBstore,
          incomingDatagramsChainA,
          incomingDatagramsChainB,
          relayerHeights,
          outgoingDatagrams

INSTANCE IBCCore

=============================================================================
