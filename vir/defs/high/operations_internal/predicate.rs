use super::super::{
    ast::{
        expression::Expression,
        position::Position,
        predicate::{visitors::PredicateWalker, Predicate},
        ty::Type,
    },
    operations_internal::ty::Typed,
};

impl Predicate {
    pub fn parameter_types(&self) -> Vec<Type> {
        match self {
            Self::LifetimeToken(_predicate) => {
                vec![]
            }
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
            Self::MemoryBlockHeapRange(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target.
                vec![
                    predicate.address.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
            Self::MemoryBlockHeapRangeGuarded(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target.
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
            Self::OwnedNonAliased(predicate) => {
                vec![predicate.place.get_type().clone()]
            }
            Self::OwnedRange(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target.
                vec![predicate.address.get_type().clone()]
            }
            Self::OwnedSet(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target of the pointer stored in the set.
                vec![predicate.set.get_type().clone()]
            }
            Self::UniqueRef(predicate) => {
                vec![predicate.place.get_type().clone()]
            }
            Self::UniqueRefRange(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target.
                vec![predicate.address.get_type().clone()]
            }
            Self::FracRef(predicate) => {
                vec![predicate.place.get_type().clone()]
            }
            Self::FracRefRange(predicate) => {
                // FIXME: This is probably wrong: we need to use the type of the
                // target.
                vec![predicate.address.get_type().clone()]
            }
        }
    }

    pub fn check_no_default_position(&self) {
        struct Checker;
        impl PredicateWalker for Checker {
            fn walk_position(&mut self, position: &Position) {
                assert!(!position.is_default());
            }
            fn walk_expression(&mut self, expression: &Expression) {
                expression.check_no_default_position();
            }
        }
        Checker.walk_predicate(self)
    }

    pub fn get_heap_location_mut(&mut self) -> Option<&mut Expression> {
        match self {
            Self::LifetimeToken(_) => None,
            Self::MemoryBlockStack(_) => None,
            Self::MemoryBlockStackDrop(_) => None,
            Self::MemoryBlockHeap(predicate) => Some(&mut predicate.address),
            Self::MemoryBlockHeapRange(predicate) => Some(&mut predicate.address),
            Self::MemoryBlockHeapRangeGuarded(predicate) => Some(&mut predicate.address),
            Self::MemoryBlockHeapDrop(predicate) => Some(&mut predicate.address),
            Self::OwnedNonAliased(predicate) => Some(&mut predicate.place),
            Self::OwnedRange(predicate) => Some(&mut predicate.address),
            Self::OwnedSet(predicate) => Some(&mut predicate.set),
            Self::UniqueRef(predicate) => Some(&mut predicate.place),
            Self::UniqueRefRange(predicate) => Some(&mut predicate.address),
            Self::FracRef(predicate) => Some(&mut predicate.place),
            Self::FracRefRange(predicate) => Some(&mut predicate.address),
        }
    }
}
