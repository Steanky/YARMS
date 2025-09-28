mod iter_ext;
mod regex_ext;

use crate::iter_ext::IteratorExt;
use crate::regex_ext::RegexExt;
use clap::{Parser, ValueEnum};
use ego_tree::iter::Edge;
use lazy_static::lazy_static;
use regex::{Regex, Replacer};
use scraper::{ElementRef, Selector};
use std::collections::HashMap;
use std::fs::OpenOptions;
use std::io;
use std::io::{BufRead, BufReader, BufWriter, ErrorKind, Read, Write};
use std::ops::Deref;
use std::str::FromStr;
use yarms_datagen_spec::protocol::packet::{PacketFieldSpec, PacketSpec};
use yarms_datagen_spec::protocol::{ProtocolSpec, ValidateOpts};
use yarms_identifier::Identifier;

#[derive(Copy, Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, ValueEnum)]
enum DataType {
    ///
    /// Generate packet data.
    Packet,
}

///
/// A command to generate JSON version files that can be read by the buildscript in `yarms-datagen`,
/// based on the contents of the Minecraft wiki.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    ///
    /// The filepath of the input HTML to parse. If this is a single `-` character, reads from
    /// standard input instead. This is the default behavior if no argument is specified.
    #[arg(short, long, default_value = "-")]
    in_file: String,

    ///
    /// The filepath where the output JSON is written. If the file doesn't exist, it is created. If
    /// it does exist the contents of the old file are "merged" with the new content.
    ///
    /// The rules for merging are simple: the (top level) `name` and `doc` values are untouched
    /// (they will not be overwritten). The entries under `packet_type_spec` will be reordered such
    /// that they are alphabetically organized based on their key, but no new entries will be
    /// inserted and none will be deleted. New packets will be freely added, old packets will be
    /// preserved.
    ///
    /// Use --overwrite-doc to allow the program to update existing documentation.
    #[arg(short, long)]
    out_file: String,

    ///
    /// The data type to generate.
    #[arg(short, long, value_enum)]
    generate: DataType,

    ///
    /// Changes the rules for overwriting the output file. Documentation for old packets will be
    /// re-created, unless the corresponding new packet has a different number of fields. If the
    /// packets are otherwise eligible for regenerating documentation, only fields with matching
    /// names will have updated documentation.
    #[arg(long, default_value_t = false)]
    overwrite_doc: bool,
}

fn read_html_from_args(args: &Args) -> Result<String, io::Error> {
    let mut string = String::new();
    if &args.in_file == "-" {
        for line in io::stdin().lock().lines() {
            string.push_str(&line?);
        }
    } else {
        let mut file = OpenOptions::new().read(true).open(&args.out_file)?;
        file.read_to_string(&mut string)?;
    }

    Ok(string)
}

fn main() -> Result<(), io::Error> {
    let args = Args::parse();
    let html_string = read_html_from_args(&args)?;

    match args.generate {
        DataType::Packet => generate_packets(args, html_string),
    }
}

fn generate_packets(args: Args, string: String) -> Result<(), io::Error> {
    let html = scraper::html::Html::parse_document(string.as_str());

    let table_selector = Selector::parse("table.wikitable").unwrap();
    let table_body_selector = Selector::parse("tbody").unwrap();
    let table_row_selector = Selector::parse("tr").unwrap();
    let table_header_selector = Selector::parse("th").unwrap();

    let packets = html
        .select(&table_selector)
        .filter_map(|item| {
            item.select(&table_body_selector)
                .next()
                .and_then(|body| body.select(&table_row_selector).next())
                .and_then(|header| header.select(&table_header_selector).next())
                .map(|inner| inner.text())
                .as_mut()
                .and_then(Iterator::next)
                .filter(|text| text.to_ascii_lowercase() == "packet id")
                .map(|_| item)
        })
        .map(parse_table)
        .collect::<Vec<_>>();

    packets
        .iter()
        .filter_map(|result| result.as_ref().err())
        .for_each(|err| {
            println!("{}", err);
            println!()
        });

    let mut good_packets = packets
        .into_iter()
        .filter_map(|result| result.ok())
        .collect::<Vec<_>>();

    let mut protocol_spec = ProtocolSpec {
        id: 0,
        packet_type_spec: Default::default(),
        packet: good_packets,
        packet_data: Default::default(),
    };

    if std::fs::exists(&args.out_file)? {
        let out_file_read = OpenOptions::new().read(true).open(&args.out_file)?;

        let mut buffer = Vec::new();
        let mut buf_read = BufReader::new(out_file_read);

        buf_read.read_to_end(&mut buffer)?;

        let mut old_version_spec = serde_json::from_slice::<ProtocolSpec>(&buffer[..])?;
        protocol_spec.id = old_version_spec.id;
        protocol_spec.packet_type_spec = old_version_spec.packet_type_spec;
        protocol_spec.packet_data = old_version_spec.packet_data;

        let mut new_packets = protocol_spec
            .packet
            .iter()
            .map(|p| ((p.name.clone(), p.clientbound), p.clone()))
            .collect::<HashMap<_, _>>();

        let old_packets = old_version_spec
            .packet
            .iter()
            .map(|p| ((p.name.clone(), p.clientbound), p.clone()))
            .collect::<HashMap<_, _>>();

        let mut merged_packets = Vec::new();
        for (key, mut old_packet) in old_packets {
            match new_packets.remove(&key) {
                None => merged_packets.push(old_packet),
                Some(new_packet) => {
                    if new_packet.fields.len() != old_packet.fields.len() {
                        merged_packets.push(old_packet);
                        continue;
                    }

                    if args.overwrite_doc {
                        old_packet.doc = new_packet.doc;

                        for (old, new) in old_packet.fields.iter_mut().zip(new_packet.fields) {
                            if old.name == new.name {
                                old.doc = new.doc;
                            }
                        }
                    }

                    merged_packets.push(old_packet);
                }
            }
        }

        // remaining packets are ones that don't exist in old_packets, so just add them
        for new_packet in new_packets.into_values() {
            merged_packets.push(new_packet);
        }

        protocol_spec.packet = merged_packets;
    }

    // guarantee consistent order
    protocol_spec.packet.sort();
    protocol_spec.packet_data.sort();

    if let Err(msg) =
        yarms_datagen_spec::protocol::validate_protocol_spec(&protocol_spec, ValidateOpts::new())
            .map_err(|messages| messages.join("\n"))
    {
        println!("{}", msg);
        println!()
    }

    let out_file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(&args.out_file)?;

    let mut writer = BufWriter::new(out_file);
    serde_json::to_writer_pretty(&mut writer, &protocol_spec)
        .map_err(|json_error| io::Error::new(ErrorKind::Other, json_error))?;

    writer.flush()?;
    Ok(())
}

///
/// The top-level type of column that packet entries are under.
#[repr(u8)]
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
enum ColumnType {
    ///
    /// Column for the packet identifier.
    PacketId = 0,

    ///
    /// Column for the packet state; i.e. whether it is intended to be sent during handshaking,
    /// login, play, etc.
    State = 1,

    ///
    /// Whether the packet is clientside or server side.
    BoundTo = 2,

    ///
    /// Name of the packet field.
    FieldName = 3,

    ///
    /// Data type field.
    FieldType = 4,

    ///
    /// Documentation of the packet field.
    Notes = 5,
}

impl ColumnType {
    ///
    /// Iterates through all column types in order.
    fn iter() -> impl Iterator<Item = ColumnType> {
        static ITEMS: [ColumnType; 6] = [
            ColumnType::PacketId,
            ColumnType::State,
            ColumnType::BoundTo,
            ColumnType::FieldName,
            ColumnType::FieldType,
            ColumnType::Notes,
        ];

        ITEMS.iter().map(|c| *c)
    }
}

impl TryFrom<u8> for ColumnType {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Ok(match value {
            0 => ColumnType::PacketId,
            1 => ColumnType::State,
            2 => ColumnType::BoundTo,
            3 => ColumnType::FieldName,
            4 => ColumnType::FieldType,
            5 => ColumnType::Notes,
            _ => return Err(()),
        })
    }
}

fn parse_table(table: ElementRef<'_>) -> Result<PacketSpec, String> {
    const MAX_COLUMNS: usize = 6;
    const MAX_COLSPAN: usize = u16::MAX as usize;

    if let Some(row_definitions) = table
        .child_elements()
        .next()
        .map(|tbody| tbody.child_elements())
        .map(|td| td.collect::<Vec<_>>())
        .filter(|entries| entries.len() >= 2)
    {
        let mut doc_elements = Vec::new();
        let packet_name_element = table
            .prev_siblings()
            .filter_map(ElementRef::wrap)
            .take_while(|element| element.value().name() != "table")
            .find(|sibling| {
                let found = sibling.child_elements().any(|child| {
                    child
                        .attr("class")
                        .filter(|val| *val == "mw-headline")
                        .is_some()
                });

                if !found {
                    doc_elements.push(sibling.clone());
                }

                found
            })
            .ok_or_else(|| {
                format!(
                    "Problem finding packet name element around table `{}`",
                    table.html()
                )
            })?;

        let packet_name = extract_packet_name(packet_name_element)?;
        let packet_doc = extract_packet_documentation(doc_elements);

        let mut total_offset = 0;
        let spans = row_definitions[0]
            .child_elements()
            .zip(0..MAX_COLUMNS)
            .map(|(header, idx)| {
                let span = header
                    .attr("colspan")
                    .map(str::trim)
                    .map(usize::from_str)
                    .and_then(Result::ok)
                    .filter(|size| *size < MAX_COLSPAN)
                    .unwrap_or(1);

                let iter = (0..span, idx, total_offset);
                total_offset += span.saturating_sub(1);
                iter
            })
            .flat_map(|(span, idx, total_offset)| span.map(move |i| (idx + total_offset + i, idx)))
            .filter_map(|(k, v)| u8::try_from(v).ok().map(|v| (k, v)))
            .filter_map(|(k, v)| ColumnType::try_from(v).ok().map(|v| (k, v)))
            .collect::<HashMap<_, _>>();

        let mut table_data = HashMap::new();
        let mut column_offsets = vec![0_usize; row_definitions.len()];

        for (row_element, row_index) in row_definitions.iter().skip(1).zip(0_usize..) {
            let column_offset = *column_offsets.get(row_index).unwrap_or(&0);

            let mut entry_index = 0;
            for data_entry in row_element.child_elements() {
                let cell_width = data_entry
                    .attr("colspan")
                    .map(str::trim)
                    .and_then(|col_span| usize::from_str(col_span).ok())
                    .unwrap_or(1);

                let our_column = entry_index + column_offset;
                if let Some(key) = spans.get(&our_column) {
                    let entry = table_data.entry(*key).or_insert_with(Vec::new);
                    entry.push(data_entry.inner_html());
                }

                if let Some(rowspan) = data_entry
                    .attr("rowspan")
                    .map(str::trim)
                    .and_then(|row_span| usize::from_str(row_span).ok())
                {
                    (row_index + 1..row_index + rowspan).for_each(|row| {
                        if let Some(inner) = column_offsets.get_mut(row) {
                            *inner = our_column + 1;
                        }
                    });
                }

                entry_index += cell_width;
            }
        }

        for column_type in ColumnType::iter() {
            table_data.entry(column_type).or_insert_with(Vec::new);
        }

        return packet_spec_from_table_data(table_data, packet_name, packet_doc);
    }

    Err(format!("Invalid table format: `{}`", table.html()))
}

fn extract_packet_name(element: ElementRef<'_>) -> Result<String, String> {
    lazy_static! {
        static ref NON_IDENT_CHARACTERS: Regex =
            Regex::new("[^a-zA-Z0-9]").expect("regex should be valid");
    }

    let identifier = element
        .traverse()
        .filter_map(|edge| match edge {
            Edge::Open(e) => ElementRef::wrap(e),
            Edge::Close(_) => None,
        })
        .find(|element| {
            element
                .attr("class")
                .filter(|cls| *cls == "mw-headline")
                .is_some()
                && element.value().name() == "span"
        })
        .and_then(|element| {
            element
                .first_child()
                .and_then(|body| body.value().as_text())
        });

    // a name like Send Message (play) would be transformed to PlaySendMessage
    if let Some(id) = identifier {
        let mut without_spaces = id.replace(" ", "");

        if let Some(start) = without_spaces.find("(") {
            if let Some(r) = without_spaces
                .as_mut_str()
                .get_mut(start + 1..start.saturating_add(2))
            {
                r.make_ascii_uppercase()
            }

            if let Some(end) = without_spaces.find(")") {
                if end < start {
                    Err(format!("Malformed packet identifier: `{:?}`", id))
                } else {
                    Ok(format!(
                        "{}{}",
                        &without_spaces[start + 1..end],
                        &without_spaces[..start]
                    ))
                }
            } else {
                Ok(format!(
                    "{}{}",
                    &without_spaces[start + 1..],
                    &without_spaces[..start]
                ))
            }
        } else {
            Ok(without_spaces)
        }
    } else {
        Err(format!(
            "Could not extract packet name from HTML: `{}`",
            element.html()
        ))
    }
    .map(|name| NON_IDENT_CHARACTERS.replace_all_owned(name, ""))
}

fn clean_documentation_string(result: String) -> String {
    lazy_static! {
        // fixes spaces before punctuation that shouldn't be there
        static ref SPACE_BEFORE_PUNCTUATION: Regex = Regex::new(r#" +(?<punc>[[:punct:]&&[^({\["'`=\-+]])"#).expect("invalid regex");

        // fixes repeat spaces and spaces after parenthesis
        static ref EXCESSIVE_SPACES: Regex = Regex::new(r"(?<punc>[[:punct:]] |\(| ) +").expect("invalid regex");

        // fixes text like first.second -> first. second
        static ref MISSING_SPACES: Regex = Regex::new(r"(?<fwd>[[:word:]])(?<punc>[.,;\])}])(?<swd>[A-Z])").expect("invalid regex");
    }

    fn quote_fixer_9000(input: &mut String, quotechar: char) {
        let mut indices = input.char_indices().rev().peekable();
        let mut ranges = Vec::new();

        while indices.peek().is_some() {
            let mut first_quote_idx = 0;
            let mut first_nonspace_char = 0;

            for (idx, char) in &mut indices {
                if char == quotechar {
                    first_quote_idx = idx;
                    break;
                }
            }

            for (idx, char) in &mut indices {
                if char != ' ' {
                    first_nonspace_char = idx;
                    break;
                }
            }

            for (_, char) in &mut indices {
                if char == quotechar {
                    break;
                }
            }

            let range = first_nonspace_char + 1..first_quote_idx;
            if !range.is_empty() {
                ranges.push(range);
            }
        }

        for range in ranges {
            input.replace_range(range, "");
        }
    }

    // clean up the documentation with some regex passes
    // this should remove artifacting such as extra spaces where links or other elements used to be
    // can't be 100% perfect, manual fixes will usually be necessary
    let result = SPACE_BEFORE_PUNCTUATION.replace_all_owned(result, "$punc");
    let result = EXCESSIVE_SPACES.replace_all_owned(result, "$punc");
    let mut result = MISSING_SPACES.replace_all_owned(result, "$fwd$punc $swd");

    // fix questionable whitespace around quotation marks
    // can't be done with a regex as it requires being aware of the block of text being quoted
    quote_fixer_9000(&mut result, '"');
    quote_fixer_9000(&mut result, '\'');

    // there are infinitely many additional processing steps we could take
    // but there would be diminishing returns, so this is good enough for now
    result
}

fn extract_packet_documentation(doc_elements: Vec<ElementRef>) -> String {
    let result = doc_elements
        .iter()
        .rev()
        .map(|element| {
            element
                .traverse()
                .filter_map(|node| {
                    match node {
                        Edge::Open(node) => node,
                        _ => return None,
                    }
                    .value()
                    .as_text()
                    .map(|text| &**text)
                    .map(str::trim)
                })
                .filter(|s| !s.is_empty())
                .join(" ")
        })
        .filter(|s| !s.trim().is_empty())
        .join("\n\n");

    clean_documentation_string(result)
}

fn merge_text(html_frag: &str, sep: &str) -> String {
    scraper::html::Html::parse_fragment(html_frag)
        .tree
        .nodes()
        .filter_map(|node| node.value().as_text())
        .map(|text| text.deref().trim())
        .filter(|s| !s.is_empty())
        .join(sep)
}

///
/// Generates a packet specification from the table data, its name, and documentation.
///
/// # Panics
/// This function may panic if the `data` hashmap does not contain entries for all the variants of
/// [`ColumnType`].
fn packet_spec_from_table_data(
    data: HashMap<ColumnType, Vec<String>>,
    name: String,
    mut doc: String,
) -> Result<PacketSpec, String> {
    let packet_id_raw = data[&ColumnType::PacketId].iter().join("");
    let state_raw = data[&ColumnType::State].iter().join("");
    let bound_raw = data[&ColumnType::BoundTo].iter().join("");

    let clientbound = match bound_raw.as_str().trim() {
        "Client" => true,
        "Server" => false,
        _ => {
            return Err(format!(
                "Packet `{}` specified invalid direction `{}`",
                name, bound_raw
            ))
        }
    };

    let packet_id_text = merge_text(packet_id_raw.as_str(), "");
    let state_text = merge_text(state_raw.as_str(), "");

    let split = packet_id_text.split(":").collect::<Vec<_>>();
    if split.len() != 3 {
        return Err(format!(
            "Packet `{}` does not specify its protocol identifier",
            name
        ));
    }

    let resource = split[2].trim();
    if !Identifier::is_valid_identifier(resource) {
        return Err(format!(
            "Packet `{}` specified an invalid resource identifier",
            name
        ));
    }

    let protocol_string = split[1]
        .to_lowercase()
        .replace("resource", "")
        .replace("0x", "");

    let protocol_id = i32::from_str_radix(protocol_string.trim(), 16).map_err(|_| {
        format!(
            "Packet `{}` had a malformed protocol identifier string: {}",
            name, protocol_string
        )
    })?;

    let fields = match gen_fields(
        &data[&ColumnType::FieldName],
        &data[&ColumnType::FieldType],
        &data[&ColumnType::Notes],
    ) {
        Ok(fields) => fields,
        Err(msg) => {
            println!("Manual intervention required for `{}`: {}", &name, &msg);
            Vec::new()
        }
    };

    if doc.is_empty() {
        doc = "Documentation is missing for this packet.".to_string();
    }

    Ok(PacketSpec {
        name,
        resource: resource.to_string(),
        doc,
        packet_id: protocol_id,
        state: state_text,
        clientbound,
        fields,
    })
}

fn name_to_ident(string: &mut String) {
    lazy_static! {
        static ref NON_IDENT_CHARACTERS: Regex =
            Regex::new("[^a-z0-9_]").expect("regex should be valid");
    }

    string.make_ascii_lowercase();

    let new = string.trim().to_string();
    let new = new.replace(" ", "_");
    let new = NON_IDENT_CHARACTERS.replace_all_owned(new, "");

    *string = new;
}

fn gen_field_spec(name: String, mut ty: String, note: String) -> PacketFieldSpec {
    lazy_static! {
        static ref PARENTHESIS: Regex =
            Regex::new(r#"\([0-9]*\)"#).expect("regex should have been valid");
        static ref EXTRA_SPACES: Regex =
            Regex::new(r#"(?<sp> ) +"#).expect("regex should have been valid");
    }

    ty.make_ascii_lowercase();

    let ty = PARENTHESIS.replace_all_owned(ty, "");
    let ty = EXTRA_SPACES.replace_all_owned(ty, "$sp");

    let ty = ty.trim().to_string();
    let ty = ty.replace(" ", "_");

    let mut doc = clean_documentation_string(note);
    if doc.is_empty() {
        doc = "Documentation is missing for this field.".to_string();
    }

    PacketFieldSpec {
        name,
        doc,
        protocol_type: ty,
    }
}

///
/// Generates fields for a packet.
///
/// Returns an error if the fields can't be determined. Generally in this case they would need to be
/// manually added instead.
fn gen_fields(
    names: &Vec<String>,
    types: &Vec<String>,
    notes: &Vec<String>,
) -> Result<Vec<PacketFieldSpec>, String> {
    if names.len() == 1 {
        if *&names[0].to_ascii_lowercase().contains("no fields") {
            // this packet appears to have no fields
            return Ok(Vec::new());
        }
    }

    if names.len() != types.len() {
        return Err("Mismatched name and length columns".to_string());
    }

    if names.is_empty() {
        // another way we can have no fields
        return Ok(Vec::new());
    }

    let mut fields = Vec::with_capacity(names.len());
    for idx in 0..names.len() {
        let mut name = merge_text(&names[idx].trim(), " ");
        let ty = merge_text(&types[idx].trim(), " ");
        let note = merge_text(
            &notes
                .get(idx)
                .map(String::as_str)
                .map(str::trim)
                .unwrap_or(""),
            " ",
        );

        name_to_ident(&mut name);
        fields.push(gen_field_spec(name, ty, note));
    }

    Ok(fields)
}
