//!
//! Build script for automatically generating Minecraft packets, and really anything that's
//! version-specific that the server cares about.

use quote::{format_ident, quote};
use std::borrow::Cow;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::error::Error;
use std::ffi::OsString;
use std::fmt::{Debug, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::path::PathBuf;
use std::process::ExitCode;
use std::str::FromStr;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use yarms_datagen_spec::protocol::{packet, ProtocolSpec, ValidateOpts};

///
/// Contextual error information.
struct ErrorContext<T> {
    file: Option<String>,
    loc: Option<String>,
    inner: T,
}

impl<T> Debug for ErrorContext<T>
where
    T: Debug + Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(file) = &self.file {
            match &self.loc {
                None => write!(f, "[{file}] -> ")?,
                Some(loc) => write!(f, "[{file} @ {loc}] -> ")?,
            }
        }

        write!(f, "{}", self.inner)
    }
}

impl<T> ErrorContext<T> {
    ///
    /// Gets a mutable reference to the "file" field of this error context.
    fn file_mut(&mut self) -> &mut Option<String> {
        &mut self.file
    }
}

///
/// Used internally to encapsulate problems with the code generation.
#[derive(Debug)]
enum BuildError {
    ///
    /// An error with build configuration (malformed environment vars, etc.)
    Configuration(ErrorContext<Cow<'static, str>>),

    ///
    /// Something was obviously wrong with a version specification: for example, a packet had an
    /// invalid resource identifier.
    Protocol(ErrorContext<Cow<'static, str>>),

    ///
    /// An I/O related error.
    Io(ErrorContext<std::io::Error>),

    ///
    /// An error parsing the JSON version files.
    Json(ErrorContext<serde_json::Error>),

    ///
    /// An error parsing the generated source code.
    Syn(ErrorContext<syn::Error>),
}

impl BuildError {
    fn context_mut(&mut self) -> &mut Option<String> {
        match self {
            BuildError::Configuration(c) => c.file_mut(),
            BuildError::Protocol(c) => c.file_mut(),
            BuildError::Io(c) => c.file_mut(),
            BuildError::Json(c) => c.file_mut(),
            BuildError::Syn(c) => c.file_mut(),
        }
    }
}

impl Display for BuildError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BuildError::Configuration(e) => write!(f, "Configuration: {e:?}"),
            BuildError::Protocol(e) => write!(f, "Protocol: {e:?}"),
            BuildError::Io(e) => write!(f, "I/O: {e:?}"),
            BuildError::Json(e) => write!(f, "JSON parsing: {e:?}"),
            BuildError::Syn(e) => write!(f, "Source code parsing: {e:?}"),
        }
    }
}

impl Error for BuildError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            BuildError::Io(e) => Some(&e.inner),
            BuildError::Json(e) => Some(&e.inner),
            BuildError::Syn(e) => Some(&e.inner),
            _ => None,
        }
    }
}

impl From<std::io::Error> for BuildError {
    fn from(value: std::io::Error) -> Self {
        BuildError::Io(ErrorContext {
            file: None,
            loc: None,
            inner: value,
        })
    }
}

impl From<serde_json::Error> for BuildError {
    fn from(value: serde_json::Error) -> Self {
        BuildError::Json(ErrorContext {
            file: None,
            loc: None,
            inner: value,
        })
    }
}

impl From<syn::Error> for BuildError {
    fn from(value: syn::Error) -> Self {
        BuildError::Syn(ErrorContext {
            file: None,
            loc: None,
            inner: value,
        })
    }
}

///
/// Entry point. All direct communication with Cargo through e.g. `println!` should happen here.
/// Actual code generation heavy lifting happens in [`build`].
///
/// Writes to the following environment variables:
/// * `YARMS_DATAGEN_CODEFILE`: a path to the file which contains all the generated source code;
/// handed off to `rustc` for use in yarms-datagen. This path is native to the system that is
/// building this library.
///
/// # Panics
/// A panic indicates either running out of memory, or a bug; they should not happen normally.
fn main() -> ExitCode {
    // re-run the script only if something in ./protocol changes
    println!("cargo::rerun-if-changed=protocol");

    match build() {
        Ok(generated_code_path) => {
            let mut string = OsString::from("cargo::rustc-env=YARMS_DATAGEN_CODEFILE=");
            string.push(&generated_code_path);
            string.push("\n");

            if let Err(err) = std::io::stdout().write_all(string.as_bytes()) {
                println!("cargo::error=Problem writing to `stdout`: {err}");
                ExitCode::FAILURE
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(build_error) => {
            println!("cargo::error={build_error}");
            ExitCode::FAILURE
        }
    }
}

///
/// Generate everything.
static FEATURE_ALL: &str = "all";

///
/// Generate packets.
static FEATURE_PACKET: &str = "packet";

///
/// Actually generate the source code, and write it to the file at `${OUT_DIR}/generated.rs`.
/// Return this file path.
///
/// Reads the following environment variables:
/// * `OUT_DIR`: should be set by Cargo; it's the directory where we place our generated sources.
/// * `CARGO_CFG_FEATURE`: also set by Cargo; specifies currently enabled features. Needed to
/// figure out what exactly we want to generate.
/// * `CARGO_CFG_YARMS_PVN`: the PVN (protocol version number) we are targeting. If
/// empty/unspecified, will default to `9999`, a "special" version that only generates a few
/// testing sources. This is set indirectly via the environment variable `YARMS_PVN`, which itself
/// is set using --cfg in RUSTFLAGS.
///
/// # Panics
/// This function should never panic, unless we run out of memory, or there's a bug. Any problems
/// with source generation should instead return a descriptive `Err`, which is communicated back to
/// Cargo with `cargo::error=${error}`.
fn build() -> Result<PathBuf, BuildError> {
    let out_dir = std::env::var_os("OUT_DIR").ok_or_else(|| {
        BuildError::Configuration(ErrorContext {
            file: None,
            loc: None,
            inner: Cow::Borrowed("required environment variable `OUT_DIR` did not exist"),
        })
    })?;

    let mut protocol_dir = std::env::current_dir()?;
    protocol_dir.push("protocol");

    let mut target_file = PathBuf::from(out_dir);
    target_file.push("generated.rs");

    let mut output_file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&target_file)?;

    let supported_features = HashSet::from([FEATURE_ALL, FEATURE_PACKET]);

    let requested_features = std::env::var_os("CARGO_CFG_FEATURE")
        .as_ref()
        .and_then(|v| v.to_str())
        .map(|str| str.split(','))
        .map(|split| {
            split
                .map(str::trim)
                .filter(|opt| !opt.is_empty() && supported_features.contains(opt))
                .map(str::to_owned)
        })
        .map(|split| split.collect::<HashSet<_>>())
        .unwrap_or_else(HashSet::new);

    let pvn_str = std::env::var_os("CARGO_CFG_YARMS_PVN").unwrap_or_else(|| OsString::from("9999"));

    let requested_protocol_versions = pvn_str
        .to_str()
        .ok_or_else(|| {
            BuildError::Configuration(ErrorContext {
                file: None,
                loc: None,
                inner: Cow::Borrowed("value of `YARMS_PVN` must be valid UTF-8"),
            })
        })?
        .split(',')
        .map(str::trim)
        .filter(|v| !v.is_empty())
        .map(i32::from_str)
        .collect::<Result<HashSet<_>, _>>()
        .map_err(|_| {
            BuildError::Configuration(ErrorContext {
                file: None,
                loc: None,
                inner: Cow::Borrowed(
                    "one or more values in `YARMS_PVN` cannot be converted to a `u32`",
                ),
            })
        })?;

    let mut read_opt = OpenOptions::new();
    read_opt.read(true);

    let mut supported_protocol_versions = std::fs::read_dir(protocol_dir)?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().filter(|ext| *ext == "json").is_some())
        .filter_map(|path| {
            path.file_stem()
                .and_then(|name| name.to_str())
                .map(str::trim)
                .and_then(|name| i32::from_str(name).ok())
                .filter(|version| requested_protocol_versions.contains(version))
                .map(|version| (version, path))
        })
        .filter_map(|(version, path)| {
            read_opt
                .open(path)
                .ok()
                .map(|file| (version, BufReader::new(file)))
        })
        .collect::<HashMap<_, _>>();

    if let Some(unsupported_version) = requested_protocol_versions
        .iter()
        .find(|version| !supported_protocol_versions.contains_key(version))
    {
        return Err(BuildError::Configuration(ErrorContext {
            file: None,
            loc: None,
            inner: Cow::Owned(format!(
                "`YARMS_PVN` specified unsupported protocol version {unsupported_version}"
            )),
        }));
    }

    let mut requested_protocol_versions =
        requested_protocol_versions.into_iter().collect::<Vec<_>>();

    // ensure consistent ordering of versions in the output file
    requested_protocol_versions.sort_unstable();

    // input data from our <PVN>.json file(s) are accumulated here
    // cleared after every file is processed, to re-use the allocation
    let mut read_buffer = Vec::new();

    // all generated code is accumulated in this string, for eventual formatting
    let mut generated_code = String::new();

    for version in requested_protocol_versions {
        supported_protocol_versions
            .get_mut(&version)
            .expect("version should have existed")
            .read_to_end(&mut read_buffer)
            .map_err(|io_err| {
                BuildError::Io(ErrorContext {
                    file: None,
                    loc: None,
                    inner: io_err,
                })
            })
            .and_then(|_| {
                gen_protocol_version(
                    &read_buffer[..],
                    &mut generated_code,
                    version,
                    &requested_features,
                )
            })
            .map_err(|mut error| {
                let ctx = error.context_mut();
                if ctx.is_none() {
                    *ctx = Some(format!("protocol/{version}.json"))
                }

                error
            })?;

        // reset the common buffer before moving on to the next version
        read_buffer.clear();
    }

    let file = syn::parse_str::<syn::File>(&generated_code)?;

    // makes the generated code actually readable
    let formatted_file = prettyplease::unparse(&file);

    output_file.write_all(formatted_file.as_bytes())?;
    output_file.flush()?;

    Ok(target_file)
}

fn has_feature(feature: &str, feature_set: &HashSet<String>) -> bool {
    feature_set.contains(feature) || feature_set.contains(FEATURE_ALL)
}

fn gen_protocol_version(
    input: &[u8],
    output: &mut String,
    protocol_version: i32,
    features: &HashSet<String>,
) -> Result<(), BuildError> {
    let mut protocol_spec = serde_json::from_slice::<ProtocolSpec>(input)?;

    if protocol_spec.id != protocol_version {
        return Err(BuildError::Configuration(ErrorContext {
            file: None,
            loc: None,
            inner: Cow::Owned(format!(
                "`id` field is {}, but file is named {}.json",
                protocol_spec.id, protocol_version
            )),
        }));
    }

    // basic sanity checks on the json we are reading from
    // this won't ever exhaustively validate the data
    // it's intended to catch common mistakes and provide a nice error message
    yarms_datagen_spec::protocol::validate_protocol_spec(
        &protocol_spec,
        ValidateOpts::new().allow_missing_packet_typedefs(),
    )
    .map_err(|err_msg| {
        BuildError::Protocol(ErrorContext {
            file: None,
            loc: None,
            inner: Cow::Owned(err_msg.join("\n")),
        })
    })?;

    let mut mod_body = quote! {};

    if has_feature(FEATURE_PACKET, features) {
        // ensures stable ordering of generated packets, even if the input .json changes
        protocol_spec.packet.sort_unstable();
        protocol_spec.packet_data.sort_unstable();

        mod_body.extend(gen_packets(
            &protocol_spec.packet,
            &protocol_spec.packet_data,
            &protocol_spec.packet_type_spec,
            protocol_version,
        )?);
    }

    let protocol_mod_doc =
        format!("Generated code to support protocol version {protocol_version}.");
    let protocol_mod_name = format_ident!("pvn_{protocol_version}");
    static PROTOCOL_VERSION_DOC: &str = "The protocol version number supported by this module.";

    let outer = quote! {
        #[doc = #protocol_mod_doc]
        pub mod #protocol_mod_name {
            #[doc = #PROTOCOL_VERSION_DOC]
            pub const PROTOCOL_VERSION_NUMBER: i32 = #protocol_version;

            #mod_body
        }
    };

    output.push_str(outer.to_string().as_str());
    Ok(())
}

fn gather_lifetimes(path: &syn::Path, lifetimes: &mut HashSet<syn::Lifetime>) {
    struct LifetimeVisitor<'a>(&'a mut HashSet<syn::Lifetime>);

    impl<'a, 'ast> Visit<'ast> for LifetimeVisitor<'a> {
        fn visit_generic_argument(&mut self, i: &'ast syn::GenericArgument) {
            if let syn::GenericArgument::Lifetime(lifetime) = i {
                if lifetime.ident != "static" {
                    self.0.insert(lifetime.clone());
                }
            }

            syn::visit::visit_generic_argument(self, i)
        }
    }

    let mut visitor = LifetimeVisitor(lifetimes);
    visitor.visit_path(path);
}

fn parse_ident_or_raw(name: &str, loc: Option<&str>) -> Result<syn::Ident, BuildError> {
    syn::parse_str::<syn::Ident>(&name)
        .or_else(|_| syn::parse_str::<syn::Ident>(&format!("r#{}", name)))
        .map_err(|syn_err| {
            BuildError::Syn(ErrorContext {
                file: None,
                loc: loc.map(ToOwned::to_owned),
                inner: syn_err,
            })
        })
}

fn parse_ident(name: &str) -> Result<syn::Ident, BuildError> {
    syn::parse_str::<syn::Ident>(name).map_err(|syn_err| {
        BuildError::Syn(ErrorContext {
            file: None,
            loc: Some(name.to_owned()),
            inner: syn_err,
        })
    })
}

fn parse_path(path: &str, loc: Option<&str>) -> Result<syn::Path, BuildError> {
    syn::parse_str::<syn::Path>(path).map_err(|syn_err| {
        BuildError::Syn(ErrorContext {
            file: None,
            loc: loc.map(ToOwned::to_owned),
            inner: syn_err,
        })
    })
}

fn resolve_type<'a>(name: &str, types: &'a BTreeMap<String, String>) -> &'a str {
    types
        .get(name)
        .map(String::as_str)
        .unwrap_or("::yarms_protocol::types::Unimplemented")
}

fn generics_from_lifetimes(
    requested_lifetimes: &mut HashSet<syn::Lifetime>,
    name: &syn::Ident,
) -> Option<syn::Generics> {
    if requested_lifetimes.is_empty() {
        None
    } else {
        let mut lifetimes = requested_lifetimes.drain().collect::<Vec<_>>();
        lifetimes.sort_unstable();

        Some(syn::Generics {
            lt_token: Some(syn::Token![<](name.span())),
            params: Punctuated::from_iter(
                lifetimes
                    .into_iter()
                    .map(|lifetime| syn::GenericParam::Lifetime(syn::LifetimeParam::new(lifetime))),
            ),
            gt_token: Some(syn::Token![>](name.span())),
            where_clause: None,
        })
    }
}

fn gen_packets(
    packets: &Vec<packet::PacketSpec>,
    packet_data: &Vec<packet::PacketDataSpec>,
    types: &BTreeMap<String, String>,
    protocol_version: i32,
) -> Result<impl IntoIterator<Item = proc_macro2::TokenTree>, BuildError> {
    let mut clientbound_packet_definitions = quote! {};
    let mut serverbound_packet_definitions = quote! {};
    let mut data_definitions = quote! {};

    let mut requested_lifetimes = HashSet::new();

    for packet in packets {
        let mut packet_body = quote! {};

        for field in &packet.fields {
            let name = parse_ident_or_raw(&field.name, Some(&packet.name))?;
            let protocol_type_path = parse_path(
                resolve_type(&field.protocol_type, types),
                Some(&packet.name),
            )?;

            let field_doc = field.doc.lines();
            gather_lifetimes(&protocol_type_path, &mut requested_lifetimes);

            packet_body.extend(quote! {
                #( #[doc = #field_doc] )*
                pub #name: #protocol_type_path,
            });
        }

        let packet_name = parse_ident(&packet.name)?;

        let protocol_id = packet.packet_id;
        let resource = &packet.resource;
        let clientbound = packet.clientbound;

        let packet_doc = format!(
            "{}\n\n# Packet Info\n|Protocol ID|Resource Key|State|Clientbound|\n|-|-|-|-|\n|{}|{}|{}|{}|",
            &packet.doc, packet.packet_id, &packet.resource, &packet.state, packet.clientbound
        );

        let packet_doc_lines = packet_doc.lines();
        let packet_generics = generics_from_lifetimes(&mut requested_lifetimes, &packet_name);

        let packet = quote! {
            #( #[doc = #packet_doc_lines] )*
            #[derive(::yarms_derive::Packet)]
            #[packet_id(#protocol_id)]
            #[resource(#resource)]
            #[clientbound(#clientbound)]
            pub struct #packet_name #packet_generics {
                #packet_body
            }
        };

        if clientbound {
            clientbound_packet_definitions.extend(packet);
        } else {
            serverbound_packet_definitions.extend(packet);
        }
    }

    for packet_data in packet_data {
        let mut packet_data_body = quote! {};

        for field in &packet_data.fields {
            let field_name = parse_ident_or_raw(&field.name, Some(&packet_data.name))?;
            let field_type_path = parse_path(
                resolve_type(&field.protocol_type, types),
                Some(&packet_data.name),
            )?;

            let field_doc = field.doc.lines();
            gather_lifetimes(&field_type_path, &mut requested_lifetimes);

            packet_data_body.extend(quote! {
                #( #[doc = #field_doc] )*
                pub #field_name: #field_type_path,
            });
        }

        let packet_data_name = parse_ident(&packet_data.name)?;
        let packet_data_generics =
            generics_from_lifetimes(&mut requested_lifetimes, &packet_data_name);
        let packet_data_doc = (&packet_data.doc).lines();

        data_definitions.extend(quote! {
            #( #[doc = #packet_data_doc] )*
            #[derive(::yarms_derive::Protocol, Clone, Debug)]
            pub struct #packet_data_name #packet_data_generics {
                #packet_data_body
            }
        });
    }

    let packet_doc = format!("Autogenerated packets for PVN {protocol_version}.");
    let packet_doc_lines = packet_doc.lines();
    static CLIENTBOUND_DOC: &str = "Clientbound (server-to-client) packet definitions.";
    static SERVERBOUND_DOC: &str = "Serverbound (client-to-server) packet definitions.";
    static DATA_DOC: &str = "Data structs, that are not themselves packets, but are used in packet fields, as necessary.\n\nTypes that are not version-specific, are highly fundamental, or unlikely to change between versions, should go in `yarms-protocol`.";

    let data_doc_lines = DATA_DOC.lines();
    let packet_module = quote! {
        #( #[doc = #packet_doc_lines] )*
        pub mod packet {
            #[doc = #CLIENTBOUND_DOC]
            pub mod clientbound {
                #clientbound_packet_definitions
            }

            #[doc = #SERVERBOUND_DOC]
            pub mod serverbound {
                #serverbound_packet_definitions
            }

            #( #[doc = #data_doc_lines] )*
            pub mod data {
                #data_definitions
            }
        }
    };

    Ok(packet_module)
}
