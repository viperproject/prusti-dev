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
            Self::MemoryBlockHeapDrop(predicate) => {
                vec![
                    predicate.address.get_type().clone(),
                    predicate.size.get_type().clone(),
                ]
            }
            Self::OwnedNonAliased(predicate) => {
                vec![predicate.place.get_type().clone()]
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
}
