//! Lowering from `vir::high` into `vir::polymorphic`.

use super::types::interface::HighTypeEncoderInterfacePrivate;

pub(in super::super) mod expression;
pub(in super::super) mod field;
pub(in super::super) mod function;
pub(in super::super) mod local;
pub(in super::super) mod position;
pub(in super::super) mod predicates;
pub(in super::super) mod ty;

/// A trait for converting `vir::high` into `vir::polymorphic`.
pub(super) trait IntoPolymorphic<Output> {
    fn lower(&self, encoder: &impl HighTypeEncoderInterfacePrivate) -> Output;
}
