#!/usr/bin/env bash

CONFIG_FILE=config.toml

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

hermes() {
  cargo run --bin hermes -- -c "$CONFIG_FILE" $@
}

setup() {
  hermes tx raw create-client ibc-0 ibc-1
  hermes tx raw create-client ibc-1 ibc-0
  log "0 -> 1: clients created"

  # hermes query client state ibc-0 07-tendermint-0
  # hermes query client state ibc-1 07-tendermint-0
  # log "0 -> 1: clients queried"

  # hermes tx raw update-client ibc-0 ibc-1 07-tendermint-0
  # hermes tx raw update-client ibc-1 ibc-0 07-tendermint-0
  # log "0 -> 1: clients updated"

  hermes tx raw conn-init ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 dummyconnection dummyconnection
  hermes tx raw conn-try ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 dummyconnection connection-0
  hermes tx raw conn-ack ibc-0 ibc-1 07-tendermint-0 07-tendermint-0 connection-0 connection-0
  hermes tx raw conn-confirm ibc-1 ibc-0 07-tendermint-0 07-tendermint-0 connection-0 connection-0
  log "0 -> 1: connection open"

  # hermes query connection end ibc-1 connection-0
  # hermes query connection end ibc-0 connection-0
  # log "0 -> 1: connection queried"

  hermes tx raw chan-open-init ibc-0 ibc-1 connection-0 transfer transfer defaultChannel defaultChannel
  hermes tx raw chan-open-try ibc-1 ibc-0 connection-0 transfer transfer defaultChannel channel-0
  hermes tx raw chan-open-ack ibc-0 ibc-1 connection-0 transfer transfer channel-0 channel-0
  hermes tx raw chan-open-confirm ibc-1 ibc-0 connection-0 transfer transfer channel-0 channel-0
  log "0 -> 1: channel open"

  # hermes query channel end ibc-0 transfer channel-0
  # hermes query channel end ibc-1 transfer channel-0
  # log "0 -> 1: channel queried"

  # -------------------------------------------

  hermes tx raw create-client ibc-1 ibc-2
  hermes tx raw create-client ibc-2 ibc-1
  log "1 -> 2: clients created"

  hermes tx raw conn-init ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 dummyconnection dummyconnection
  hermes tx raw conn-try ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 dummyconnection connection-1
  hermes tx raw conn-ack ibc-1 ibc-2 07-tendermint-1 07-tendermint-0 connection-1 connection-0
  hermes tx raw conn-confirm ibc-2 ibc-1 07-tendermint-0 07-tendermint-1 connection-0 connection-1
  log "1 -> 2: connection open"

  hermes tx raw chan-open-init ibc-1 ibc-2 connection-1 transfer transfer defaultChannel defaultChannel
  hermes tx raw chan-open-try ibc-2 ibc-1 connection-0 transfer transfer defaultChannel channel-1
  hermes tx raw chan-open-ack ibc-1 ibc-2 connection-1 transfer transfer channel-1 channel-0
  hermes tx raw chan-open-confirm ibc-2 ibc-1 connection-0 transfer transfer channel-0 channel-1
  log "1 -> 2: channel open"
}
