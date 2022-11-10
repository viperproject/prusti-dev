use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    middle::{
        self as vir_mid,
        operations::{TypedToMiddleExpression, TypedToMiddleRvalueLowerer, TypedToMiddleType},
    },
    typed as vir_typed,
};

impl<'v, 'tcx> TypedToMiddleRvalueLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn typed_to_middle_rvalue_expression(
        &self,
        expression: vir_typed::Expression,
    ) -> SpannedEncodingResult<vir_mid::Expression> {
        expression.typed_to_middle_expression(self)
    }

    fn typed_to_middle_rvalue_type(
        &self,
        ty: vir_typed::Type,
    ) -> Result<vir_mid::Type, Self::Error> {
        ty.typed_to_middle_type(self)
    }

    fn typed_to_middle_rvalue_unary_op_kind(
        &self,
        kind: vir_typed::UnaryOpKind,
    ) -> Result<vir_mid::UnaryOpKind, Self::Error> {
        kind.typed_to_middle_expression(self)
    }

    fn typed_to_middle_rvalue_binary_op_kind(
        &self,
        kind: vir_typed::BinaryOpKind,
    ) -> Result<vir_mid::BinaryOpKind, Self::Error> {
        kind.typed_to_middle_expression(self)
    }

    fn typed_to_middle_rvalue_lifetime_const(
        &self,
        lifetime: vir_typed::ty::LifetimeConst,
    ) -> Result<vir_mid::ty::LifetimeConst, Self::Error> {
        Ok(vir_mid::ty::LifetimeConst {
            name: lifetime.name,
        })
    }

    fn typed_to_middle_rvalue_uniqueness(
        &self,
        uniqueness: vir_typed::ty::Uniqueness,
    ) -> Result<vir_mid::ty::Uniqueness, Self::Error> {
        uniqueness.typed_to_middle_type(self)
    }

    fn typed_to_middle_rvalue_discriminant(
        &self,
        _value: vir_typed::ast::rvalue::Discriminant,
    ) -> Result<vir_mid::ast::rvalue::Discriminant, Self::Error> {
        unreachable!("Discriminant rvalue cannot be lowered")
    }
}
