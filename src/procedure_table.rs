use prusti_interface::data::ProcedureDefId;

#[derive(Debug, Clone)]
pub struct ProcedureTable {}

type Key = ProcedureDefId;
type Value = u32;

impl ProcedureTable {
    pub fn new() -> Self {
        ProcedureTable {}
    }

    pub fn get_or_init(&mut self, key: Key, epoch: u32) -> Value {
        unimplemented!()
    }

    pub fn get_required_elements(&self, epoch: u32) -> Vec<Key> {
        unimplemented!()
    }
}
