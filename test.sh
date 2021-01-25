#!/usr/bin/env bash

set -e

TIMEOUT=1000000

source test_env.sh

0_to_1() {
  local amount=$1
  local denom="samoleans"
  rrly tx raw packet-send ibc-0 ibc-1 transfer channel-0 $amount $TIMEOUT -n 1 -d $denom
  rrly tx raw packet-recv ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 transfer transfer channel-0 channel-0
  rrly tx raw packet-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 transfer transfer channel-0 channel-0

  rrly query packet unreceived-packets ibc-1 ibc-0 transfer channel-0
  rrly query packet unreceived-acks ibc-0 ibc-1 transfer channel-0

  balance
  log "0 -> 1: DONE"
}

1_to_2() {
  local amount=$1
  local denom="ibc/27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C"
  rrly tx raw packet-send ibc-1 ibc-2 transfer channel-1 $amount $TIMEOUT -n 1 -d $denom
  rrly tx raw packet-recv ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 transfer transfer channel-1 channel-0
  rrly tx raw packet-ack ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 transfer transfer channel-1 channel-0
  rrly query packet unreceived-packets ibc-2 ibc-1 transfer channel-1
  rrly query packet unreceived-acks ibc-1 ibc-2 transfer channel-0

  balance
  log "1 -> 2: DONE"
}

2_to_1() {
  local amount=$1
  local denom="ibc/F47F0D7C9B4F7D971DF647A75A80CB8D905D3230262FEF2996340664D3A12D48"
  rrly tx raw packet-send ibc-2 ibc-1 transfer channel-0 $amount $TIMEOUT -n 1 -d $denom
  rrly tx raw packet-recv ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 transfer transfer channel-0 channel-1
  # in the gaiad version with the bug, in the previous command I get:
  # tendermint@v0.34.1/consensus/state.go:379 +0x896\\n: panic\
  rrly tx raw packet-ack ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 transfer transfer channel-0 channel-1
  # in the latest gaiad version (without the bug), in the previous command I get:
  # github.com/cosmos/cosmos-sdk/x/ibc/core/04-channel/keeper.Keeper.AcknowledgePacket
  #     github.com/cosmos/cosmos-sdk@v0.40.0/x/ibc/core/04-channel/keeper/packet.go:430
  # github.com/cosmos/cosmos-sdk/x/ibc/core/keeper.Keeper.Acknowledgement
  #     github.com/cosmos/cosmos-sdk@v0.40.0/x/ibc/core/keeper/msg_server.go:592
  # github.com/cosmos/cosmos-sdk/x/ibc/core.NewHandler.func1
  #     github.com/cosmos/cosmos-sdk@v0.40.0/x/ibc/core/handler.go:83
  # github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).runMsgs
  #     github.com/cosmos/cosmos-sdk@v0.40.0/baseapp/baseapp.go:719
  # github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).runTx
  #     github.com/cosmos/cosmos-sdk@v0.40.0/baseapp/baseapp.go:664
  # github.com/cosmos/cosmos-sdk/baseapp.(*BaseApp).DeliverTx
  #     github.com/cosmos/cosmos-sdk@v0.40.0/baseapp/abci.go:261
  # github.com/tendermint/tendermint/abci/client.(*localClient).DeliverTxAsync
  #     github.com/tendermint/tendermint@v0.34.1/abci/client/local_client.go:87
  # github.com/tendermint/tendermint/proxy.(*appConnConsensus).DeliverTxAsync
  #     github.com/tendermint/tendermint@v0.34.1/proxy/app_conn.go:85
  # github.com/tendermint/tendermint/state.execBlockOnProxyApp
  #     github.com/tendermint/tendermint@v0.34.1/state/execution.go:319
  # github.com/tendermint/tendermint/state.(*BlockExecutor).ApplyBlock
  #     github.com/tendermint/tendermint@v0.34.1/state/execution.go:140
  # github.com/tendermint/tendermint/consensus.(*State).finalizeCommit
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:1569
  # github.com/tendermint/tendermint/consensus.(*State).tryFinalizeCommit
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:1487
  # github.com/tendermint/tendermint/consensus.(*State).enterCommit.func1
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:1420
  # github.com/tendermint/tendermint/consensus.(*State).enterCommit
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:1459
  # github.com/tendermint/tendermint/consensus.(*State).addVote
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:2048
  # github.com/tendermint/tendermint/consensus.(*State).tryAddVote
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:1846
  # github.com/tendermint/tendermint/consensus.(*State).handleMsg
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:803
  # github.com/tendermint/tendermint/consensus.(*State).receiveRoutine
  #     github.com/tendermint/tendermint@v0.34.1/consensus/state.go:752
  # failed to execute message; message index: 1: acknowledge packet verification failed: packet destination channel doesn't match the counterparty's channel (channel-0 ‚â† channel-1): invalid packet

  rrly query packet unreceived-packets ibc-1 ibc-2 transfer channel-0
  rrly query packet unreceived-acks ibc-2 ibc-1 transfer channel-1

  balance
  log "2 -> 1: DONE"
}

1_to_0() {
  local amount=$1
  local denom="ibc/27A6394C3F9FF9C9DCF5DFFADF9BB5FE9A37C7E92B006199894CF1824DF9AC7C"
  rrly tx raw packet-send ibc-1 ibc-0 transfer channel-0 $amount $TIMEOUT -n 1 -d $denom
  rrly tx raw packet-recv ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 transfer transfer channel-0 channel-0
  rrly tx raw packet-ack ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 transfer transfer channel-0 channel-0

  rrly query packet unreceived-packets ibc-0 ibc-1 transfer channel-0
  rrly query packet unreceived-acks ibc-1 ibc-0 transfer channel-0

  balance
  log "1 -> 0: DONE"
}

setup
balance
echo "will start..."

AMOUNT=100
0_to_1 $AMOUNT
1_to_2 $AMOUNT
2_to_1 $AMOUNT
1_to_0 $AMOUNT
echo "Done!"
