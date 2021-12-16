use super::super::{
    ast::{predicate::Predicate, ty::Type},
    operations_internal::ty::Typed,
};

impl Predicate {
    pub fn parameter_types(&self) -> Vec<Type> {
        match self {
            Self::MemoryBlockStack(predicate) => {
                vec![
                    predicate.place.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
            Self::MemoryBlockStackDrop(predicate) => {
                vec![
                    predicate.place.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
            Self::MemoryBlockHeap(predicate) => {
                vec![
                    predicate.address.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
            Self::MemoryBlockHeapDrop(predicate) => {
                vec![
                    predicate.address.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
        }
    }
}
