//!
//! Common data structures used by `yarms-datagen` and `yarms-wiki-scraper`. Most of these are
//! meant to be (de)serialized using Serde.

use serde_derive::{Deserialize, Serialize};

#[cfg(feature = "protocol")]
///
/// Data structures defining features related to protocol versions (PVNs).
pub mod protocol;

///
/// Specification for a particular version of Minecraft.
#[derive(Serialize, Deserialize)]
pub struct VersionSpec {
    #[cfg(feature = "protocol")]
    ///
    /// The corresponding protocol version.
    ///
    /// Multiple otherwise-distinct version specifications may use the same protocol version.
    pub protocol: i32,

    ///
    /// The name of this version; ex. `1.19.4`.
    pub name: String,
}
