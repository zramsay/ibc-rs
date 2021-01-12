use abscissa_core::{Component, FrameworkError, Shutdown};
use tracing_subscriber::{EnvFilter, FmtSubscriber, reload::Handle};
use tracing_subscriber::fmt::{
    format::{Format, Json, JsonFields},
    Formatter,
    time::SystemTime
};
use tracing_subscriber::util::SubscriberInitExt;

/// Abscissa component for initializing the `tracing` subsystem
#[derive(Component, Debug)]
pub struct Tracing {
    filter_handle: Handle<EnvFilter, Formatter<JsonFields, Format<Json, SystemTime>>>,
}

impl Tracing {
    /// Creates a new [`Tracing`] component with the given `filter`.
    pub fn new() -> Result<Self, FrameworkError> {
        // TODO(adi) put these into a section of the relayer configuration
        let filter = "debug".to_string();
        let use_color = false;

        // Construct a tracing subscriber with the supplied filter and enable reloading.
        let builder = FmtSubscriber::builder()
            .with_env_filter(filter)
            .with_ansi(use_color)
            .json()
            .with_filter_reloading();
        let filter_handle = builder.reload_handle();

        let subscriber = builder.finish();
        subscriber.init();

        Ok(Self {
            filter_handle,
        })
    }
}
//
// impl std::fmt::Debug for Tracing {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_struct("Tracing").finish()
//     }
// }

// impl<A: abscissa_core::Application> Component<A> for Tracing {
//     fn id(&self) -> abscissa_core::component::Id {
//         abscissa_core::component::Id::new("relayer-cli::components::Tracing")
//     }
//
//     fn version(&self) -> abscissa_core::Version {
//         abscissa_core::Version::parse("0.1.0").unwrap()
//     }
//
//     fn before_shutdown(&self, _kind: Shutdown) -> Result<(), FrameworkError> {
//         tracing::info!("shutting down");
//         Ok(())
//     }
// }