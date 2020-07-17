//! `query` subcommand

use abscissa_core::{Command, Help, Options, Runnable};

mod channel;
mod client;
mod connection;

/// `query` subcommand
#[derive(Command, Debug, Options, Runnable)]
pub enum QueryCmd {
    /// `help` subcommand
    #[options(help = "show help for a command")]
    Help(Help<Self>),

    /// The `query client` subcommand
    #[options(help = "query client")]
    Client(QueryClientCmds),

    /// The `query connection` subcommand
    #[options(help = "query connection")]
    Connection(QueryConnectionCmds),

    /// The `query channel` subcommand
    #[options(help = "query channel")]
    Channel(QueryChannelCmds),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryClientCmds {
    /// `help` subcommand
    #[options(help = "show help for a command")]
    Help(Help<Self>),

    /// The `query client state` subcommand
    #[options(help = "query client full state")]
    State(client::QueryClientStateCmd),
    /// The `query client consensus` subcommand

    /// The `query client consensus` subcommand
    #[options(help = "query client consensus")]
    Consensus(client::QueryClientConsensusCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryConnectionCmds {
    /// `help` subcommand
    #[options(help = "show help for a command")]
    Help(Help<Self>),

    /// The `query connection end` subcommand
    #[options(help = "query connection end")]
    End(connection::QueryConnectionEndCmd),
}

#[derive(Command, Debug, Options, Runnable)]
pub enum QueryChannelCmds {
    /// `help` subcommand
    #[options(help = "show help for a command")]
    Help(Help<Self>),

    /// The `query channel end` subcommand
    #[options(help = "query channel end")]
    End(channel::QueryChannelEndCmd),
}
