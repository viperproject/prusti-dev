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
            Self::LifetimeToken(predicate) => predicate.get_identifier(),
            Self::MemoryBlockStack(predicate) => predicate.get_identifier(),
            Self::MemoryBlockStackDrop(predicate) => predicate.get_identifier(),
            Self::MemoryBlockHeap(predicate) => predicate.get_identifier(),
            Self::MemoryBlockHeapRange(predicate) => predicate.get_identifier(),
            Self::MemoryBlockHeapDrop(predicate) => predicate.get_identifier(),
            Self::OwnedNonAliased(predicate) => predicate.get_identifier(),
            Self::OwnedRange(predicate) => predicate.get_identifier(),
            Self::OwnedSet(predicate) => predicate.get_identifier(),
            Self::UniqueRef(predicate) => predicate.get_identifier(),
            Self::UniqueRefRange(predicate) => predicate.get_identifier(),
            Self::FracRef(predicate) => predicate.get_identifier(),
            Self::FracRefRange(predicate) => predicate.get_identifier(),
        }
    }
}

impl WithIdentifier for predicate::LifetimeToken {
    fn get_identifier(&self) -> String {
        "LifetimeToken".to_string()
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

impl WithIdentifier for predicate::MemoryBlockHeapRange {
    fn get_identifier(&self) -> String {
        "MemoryBlockHeapRange".to_string()
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

impl WithIdentifier for predicate::OwnedRange {
    fn get_identifier(&self) -> String {
        format!("OwnedRange${}", self.address.get_type().get_identifier())
    }
}

impl WithIdentifier for predicate::OwnedSet {
    fn get_identifier(&self) -> String {
        format!("OwnedSet${}", self.set.get_type().get_identifier())
    }
}

impl WithIdentifier for predicate::UniqueRef {
    fn get_identifier(&self) -> String {
        format!("UniqueRef${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for predicate::UniqueRefRange {
    fn get_identifier(&self) -> String {
        format!(
            "UniqueRefRange${}",
            self.address.get_type().get_identifier()
        )
    }
}

impl WithIdentifier for predicate::FracRef {
    fn get_identifier(&self) -> String {
        format!("FracRef${}", self.place.get_type().get_identifier())
    }
}

impl WithIdentifier for predicate::FracRefRange {
    fn get_identifier(&self) -> String {
        format!("FracRefRange${}", self.address.get_type().get_identifier())
    }
}
