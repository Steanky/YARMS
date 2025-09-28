use serde_derive::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

///
/// A packet field definition. Includes the name, documentation, and a type.
#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct PacketFieldSpec {
    pub name: String,
    pub doc: String,
    pub protocol_type: String,
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct PacketSpec {
    pub name: String,
    pub resource: String,
    pub doc: String,
    pub packet_id: i32,
    pub state: String,
    pub clientbound: bool,
    pub fields: Vec<PacketFieldSpec>,
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct DataFieldSpec {
    pub name: String,
    pub doc: String,
    pub protocol_type: String,
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct PacketDataSpec {
    pub name: String,
    pub doc: String,
    pub fields: Vec<DataFieldSpec>,
}

impl Hash for PacketSpec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.state.hash(state);
        self.clientbound.hash(state);
        self.packet_id.hash(state);
    }
}

impl Eq for PacketSpec {}

impl PartialEq<Self> for PacketSpec {
    fn eq(&self, other: &Self) -> bool {
        self.clientbound == other.clientbound
            && self.packet_id == other.packet_id
            && self.state == other.state
    }
}

impl PartialOrd<Self> for PacketSpec {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PacketSpec {
    fn cmp(&self, other: &Self) -> Ordering {
        self.state
            .cmp(&other.state)
            .then_with(|| self.clientbound.cmp(&other.clientbound))
            .then_with(|| self.packet_id.cmp(&other.packet_id))
    }
}

impl Hash for PacketDataSpec {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl Eq for PacketDataSpec {}

impl PartialEq<Self> for PacketDataSpec {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl PartialOrd<Self> for PacketDataSpec {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PacketDataSpec {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(&other.name)
    }
}
