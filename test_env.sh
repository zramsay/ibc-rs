#!/usr/bin/env bash

CONFIG_FILE=loop_config.toml

CHAIN_0_RPC_ADDR="tcp://localhost:20600"
CHAIN_1_RPC_ADDR="tcp://localhost:20601"
CHAIN_2_RPC_ADDR="tcp://localhost:20602"

log() {
  echo
  echo
  echo
  echo "---------------- $1 ----------------"
  echo
  echo
  echo
}

balance() {
  echo "0 balance:"
  gaiad --node $CHAIN_0_RPC_ADDR query bank balances $(gaiad --home data/ibc-0 keys --keyring-backend="test" show user -a)
  echo "1 balance:"
  gaiad --node $CHAIN_1_RPC_ADDR query bank balances $(gaiad --home data/ibc-1 keys --keyring-backend="test" show user -a)
  echo "2 balance:"
  gaiad --node $CHAIN_2_RPC_ADDR query bank balances $(gaiad --home data/ibc-2 keys --keyring-backend="test" show user -a)
  log "balance shown"
}

rrly() {
  cargo run --bin relayer -- -c "$CONFIG_FILE" $@
}

setup() {
  rrly tx raw create-client ibc-0 ibc-1
  rrly tx raw create-client ibc-1 ibc-0
  log "0 -> 1: clients created"

  # rrly query client state ibc-0 07-tendermint-0
  # rrly query client state ibc-1 07-tendermint-0
  # log "0 -> 1: clients queried"

  # rrly tx raw update-client ibc-0 ibc-1 07-tendermint-0
  # rrly tx raw update-client ibc-1 ibc-0 07-tendermint-0
  # log "0 -> 1: clients updated"

  rrly tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 dummyconnection dummyconnection
  rrly tx raw conn-try ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 dummyconnection connection-0
  rrly tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 connection-0 connection-0
  rrly tx raw conn-confirm ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 connection-0 connection-0
  log "0 -> 1: connection open"

  # rrly query connection end ibc-1 connection-0
  # rrly query connection end ibc-0 connection-0
  # log "0 -> 1: connection queried"

  rrly tx raw chan-init ibc-0 ibc-1 connection-0 transfer transfer defaultChannel defaultChannel
  rrly tx raw chan-try ibc-1 ibc-0 connection-0 transfer transfer defaultChannel channel-0
  rrly tx raw chan-ack ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-0
  rrly tx raw chan-confirm ibc-1 ibc-0 connection-0 transfer transfer channel-0 channel-0
  log "0 -> 1: channel open"

  # rrly query channel end ibc-0 transfer channel-0
  # rrly query channel end ibc-1 transfer channel-0
  # log "0 -> 1: channel queried"

  # -------------------------------------------

  rrly tx raw create-client ibc-1 ibc-2
  rrly tx raw create-client ibc-2 ibc-1
  log "1 -> 2: clients created"

  rrly tx raw conn-init ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 dummyconnection dummyconnection
  rrly tx raw conn-try ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 dummyconnection connection-1
  rrly tx raw conn-ack ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 connection-1 connection-0
  rrly tx raw conn-confirm ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 connection-0 connection-1
  log "1 -> 2: connection open"

  rrly tx raw chan-init ibc-1 ibc-2 connection-1 transfer transfer defaultChannel defaultChannel
  rrly tx raw chan-try ibc-2 ibc-1 connection-0 transfer transfer defaultChannel channel-1
  rrly tx raw chan-ack ibc-1 ibc-2 connection-1 transfer transfer channel-1 channel-0
  rrly tx raw chan-confirm ibc-2 ibc-1 connection-0 transfer transfer channel-0 channel-1
  log "1 -> 2: channel open"
}
