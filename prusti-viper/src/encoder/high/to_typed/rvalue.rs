use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    high as vir_high,
    typed::{
        self as vir_typed,
        operations::{HighToTypedExpression, HighToTypedRvalueLowerer, HighToTypedType},
    },
};

impl<'v, 'tcx> HighToTypedRvalueLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn high_to_typed_rvalue_expression(
        &mut self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_typed::Expression> {
        expression.high_to_typed_expression(self)
    }

    fn high_to_typed_rvalue_type(
        &mut self,
        ty: vir_high::Type,
    ) -> Result<vir_typed::Type, Self::Error> {
        ty.high_to_typed_type(self)
    }

    fn high_to_typed_rvalue_unary_op_kind(
        &mut self,
        kind: vir_high::UnaryOpKind,
    ) -> Result<vir_typed::UnaryOpKind, Self::Error> {
        kind.high_to_typed_expression(self)
    }

    fn high_to_typed_rvalue_binary_op_kind(
        &mut self,
        kind: vir_high::BinaryOpKind,
    ) -> Result<vir_typed::BinaryOpKind, Self::Error> {
        kind.high_to_typed_expression(self)
    }

    fn high_to_typed_rvalue_lifetime_const(
        &mut self,
        lifetime: vir_high::ty::LifetimeConst,
    ) -> Result<vir_typed::ty::LifetimeConst, Self::Error> {
        Ok(vir_typed::ty::LifetimeConst {
            name: lifetime.name,
        })
    }

    fn high_to_typed_rvalue_variable_decl(
        &mut self,
        variable: vir_high::VariableDecl,
    ) -> Result<vir_typed::VariableDecl, Self::Error> {
        variable.high_to_typed_expression(self)
    }
}
