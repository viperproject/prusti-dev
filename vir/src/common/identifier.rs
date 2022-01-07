pub trait WithIdentifier {
    fn get_identifier(&self) -> String;
}

// TODO: this will need to be some extensible name, which supports all of the
// name operations that we might want to do, but is not a string.

/// Temporary standing for a name, returned by `NameInterner::intern`.
/// Can be exchanged for a real `String` name with `NameInterner::get_interned`,
/// but only once all names have been interned.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub struct NameHash(u64, u64);

impl NameHash {
    pub fn new(crate_id: u64, local_id: u64) -> Self {
        NameHash(crate_id, local_id)
    }
}
