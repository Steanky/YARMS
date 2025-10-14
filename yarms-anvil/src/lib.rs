//!
//! Support for the Anvil format [(link)](https://minecraft.wiki/w/Anvil_file_format). Provides an
//! implementation for loading NBT data from Anvil region files.
//!
//! This crate, like most of its siblings, is designed to be highly "composable" and minimally
//! opinionated. This makes it a bit harder to set up, but can be heavily customized and tweaked to
//! suit specific needs. To allow for this sort of modularity, the process of decoding a single
//! chunk is split across several stages. The following flowchart should help illustrate the
//! process:
//!
//! ```skip
//! ┌─────────────────┐
//! │ Chunk Requested │
//! └┬────────────────┘
//! ┌┴────────────────────────┐
//! │ Is our loader parallel? ├┐
//! └┬────────────────────────┘│
//!  │ Yes                     │ No
//! ┌┴───────────────────────┐┌┴──────────────────────────┐
//! │ Proceed in thread pool ││ Proceed on current thread │
//! └┬───────────────────────┘└┬──────────────────────────┘
//!  ├─────────────────────────┘
//! ┌┴─────────────────────────────────────────────┐
//! │ Load region corresponding to requested chunk │
//! └┬─────────────────────────────────────────────┘
//! ┌┴───────────────────────┐ No ┌────────────────────────┐
//! │ Does the region exist? ├────┤ No chunk to load, exit ├┐
//! └┬───────────────────────┘    └────────────────────────┘│
//!  │ Yes                                                  │
//! ┌┴───────────────────────────────────────────────────┐  │
//! │ Look up the Anvil header data for our region       │  │
//! │ If it's not cached, load from our region and cache │  │
//! └┬───────────────────────────────────────────────────┘  │
//! ┌┴────────────────────────────────┐                     │
//! │ Does the requested chunk exist? │ No                  │
//! │ (according to the header data)  ├─────────────────────┘
//! └┬────────────────────────────────┘
//!  │ Yes
//! ┌┴─────────────────────────────────────┐
//! │ Load the chunk data from the region. │
//! │ Decompress it if necessary, then     │
//! │ parse the NBT data                   │
//! └┬─────────────────────────────────────┘
//! ┌┴──────────────────────────────────────┐
//! │ Invoke the callback with the NBT data │
//! └───────────────────────────────────────┘
//! ```
//!
//! Different traits encapsulate different steps in this diagram.
//! [`yarms_chunk_loader::ChunkLoader`] implementations (such as [`crate::loader::AnvilLoader`])
//! accept a request for a chunk at specific chunk coordinates, as well as a callback function to
//! be invoked when (if?) the chunk is loaded. (A callback is used rather than returning an object
//! to allow borrowing from internal buffers).
//!
//! `ChunkLoader`s that can load in parallel with the calling thread implement
//! [`yarms_chunk_loader::ThreadedChunkLoader`]. `AnvilLoader` supports parallel loading if it is
//! constructed using thread-safe components.
//!
//! Regardless of whether the loader is parallel or not, after receiving a request for a chunk, the
//! loader attempts to load a region from a [`crate::region::RegionLoader`]. This corresponds to a
//! specific .mca file (in the case of Anvil data loaded from a typical Minecraft world). An
//! individual region covers 32x32 chunks. If the region can't be found, the chunk doesn't exist
//! and so there's nothing more to do.
//!
//! If it does exist, the next step is to look at the Anvil header data, which is part of the
//! region. The header data contains information about where chunks are located inside of the
//! region. It also tells us if the chunk exists or not. The header data is cached for future use,
//! if it wasn't already. Header parsing and caching is managed by [`crate::header::HeaderLookup`].
//!
//! If our chunk is present in the region, we load it from the location indicated by the header
//! data. It may appear in the following formats:
//! * GZIP
//! * ZLIB
//! * Uncompressed
//! * LZ4 (requires the `lz4` feature)
//!
//! A [`crate::chunk_decoder::ChunkDecoder`] implementation is responsible for loading and
//! decompressing a chunk, after being handed the necessary information to find the data within the
//! region. Finally, the decoder parses the NBT and invokes the callback function with a tag, which
//! may contain borrowed data.
//!

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

///
/// A very simple growable buffer of bytes based on `Vec`.
pub mod buffer;

///
/// Decoding chunks from an I/O source.
pub mod chunk_decoder;

///
/// Reading chunks.
pub mod loader;

///
/// Support for loading Anvil regions from some I/O source.
pub mod region;

///
/// Anvil headers (chunk table).
pub mod header;

use alloc::string::String;
use alloc::string::ToString;
use core::str::FromStr;

///
/// Compute the Anvil region file name given the region coordinates.
///
/// Example usage:
///
/// ```
/// use yarms_anvil::region_to_file_name;
///
/// let name = region_to_file_name(42, -10);
/// assert_eq!(name, "r.42.-10.mca");
///
/// ```
#[must_use]
pub fn region_to_file_name(region_x: i32, region_z: i32) -> String {
    let mut file_name = String::with_capacity(16);

    let x_string = region_x.to_string();
    let z_string = region_z.to_string();

    file_name.push('r');
    file_name.push('.');
    file_name.push_str(&x_string);
    file_name.push('.');
    file_name.push_str(&z_string);
    file_name.push('.');
    file_name.push_str("mca");

    file_name
}

///
/// Inverse of [`region_to_file_name`]. Converts a filename to its corresponding region coordinates.
/// Returns `None` if the format is not as expected.
///
/// ```
/// use yarms_anvil::region_from_file_name;
///
/// let file_name = "r.42.-10.mca";
/// let pair = region_from_file_name(file_name).expect("should be a valid Anvil filename");
///
/// assert_eq!(pair, (42, -10))
///
/// ```
#[must_use]
pub fn region_from_file_name(name: &str) -> Option<(i32, i32)> {
    let mut array = [""; 4];

    // moderately more complex but avoids needing to alloc a Vec
    name.splitn(4, '.')
        .zip(0..)
        .for_each(|(part, idx)| array[idx] = part);

    if array[0] != "r" || array[3] != "mca" {
        return None;
    }

    let region_x = i32::from_str(array[1]).ok()?;
    let region_z = i32::from_str(array[2]).ok()?;

    Some((region_x, region_z))
}

#[cfg(test)]
mod tests {
    use crate::region::CursorRegionLoader;
    use std::cell::RefCell;
    use std::io::Cursor;
    use std::vec::Vec;
    use yarms_chunk_loader::ChunkLoader;
    use yarms_nbt::keys;
    use yarms_nbt::tag;

    #[test]
    fn simple_load() {
        let anvil_bytes = include_bytes!("r.0.0.mca");
        let anvil_bytes = Vec::from(anvil_bytes);

        let cursor = Cursor::new(anvil_bytes);

        let mut map = hashbrown::HashMap::with_capacity(1);
        map.insert((0, 0), yarms_std::io::IOWrapper(cursor));

        let loader = crate::loader::builder()
            .with_no_pool()
            .with_region_loader(RefCell::new(CursorRegionLoader::new(map)))
            .with_standard_decoder(RefCell::new(None))
            .with_lru_header_lookup(1)
            .with_basic_buffers()
            .build();

        let result = loader.load_chunk_sync(0, 0, |chunk_opt| {
            let data = chunk_opt.expect("chunk data should have been present");
            assert_eq!(data.get(&keys!("zPos")), Some(&tag!(Int["zPos"]: 0)));
            assert_eq!(data.get(&keys!("xPos")), Some(&tag!(Int["xPos"]: 0)));

            // the chunk data has a book in it. make sure we loaded everything correctly
            // by verifying that the contents are as expected.
            assert_eq!(data.get(&keys!("block_entities",
                0,
                "Items",
                0,
                "components",
                "minecraft:written_book_content",
                "pages",
                0,
                "raw")),
                Some(&tag!(String["raw"]: "This is an item used for testing.\nHello yarms-anvil-loader!")));

            true
        });

        assert!(
            result.expect("chunk should have loaded without error"),
            "returned value wasn't true"
        );
    }
}
