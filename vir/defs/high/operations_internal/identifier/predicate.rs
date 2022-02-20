use super::{
    super::{
        super::ast::predicate::{self, Predicate},
        ty::Typed,
    },
    common::append_type_arguments,
};
use crate::common::identifier::WithIdentifier;

impl WithIdentifier for Predicate {
    fn get_identifier(&self) -> String {
        match self {
            Self::MemoryBlockStack(predicate) => predicate.get_identifier(),
            Self::MemoryBlockStackDrop(predicate) => predicate.get_identifier(),
            Self::MemoryBlockHeap(predicate) => predicate.get_identifier(),
            Self::MemoryBlockHeapDrop(predicate) => predicate.get_identifier(),
            Self::OwnedNonAliased(predicate) => predicate.get_identifier(),
        }
    }
}

impl WithIdentifier for predicate::MemoryBlockStack {
    fn get_identifier(&self) -> String {
        "MemoryBlockStack".to_string()
    }
}

impl WithIdentifier for predicate::MemoryBlockStackDrop {
    fn get_identifier(&self) -> String {
        "MemoryBlockStackDrop".to_string()
    }
}

impl WithIdentifier for predicate::MemoryBlockHeap {
    fn get_identifier(&self) -> String {
        "MemoryBlockHeap".to_string()
    }
}

impl WithIdentifier for predicate::MemoryBlockHeapDrop {
    fn get_identifier(&self) -> String {
        "MemoryBlockHeapDrop".to_string()
    }
}

impl WithIdentifier for predicate::OwnedNonAliased {
    fn get_identifier(&self) -> String {
        format!("OwnedNonAliased${}", self.place.get_type().get_identifier())
    }
}
