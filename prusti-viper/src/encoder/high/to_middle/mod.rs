use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    high::{self as vir_high},
    middle::{
        self as vir_mid,
        operations::{TypedToMiddleExpression, TypedToMiddleTypeDecl},
    },
    typed::operations::{HighToTypedExpression, HighToTypedTypeDecl},
};

pub trait HighToMiddle {
    type Output;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output>;
}

impl HighToMiddle for vir_high::Expression {
    type Output = vir_mid::Expression;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}

impl HighToMiddle for vir_high::VariableDecl {
    type Output = vir_mid::VariableDecl;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}

impl HighToMiddle for vir_high::Type {
    type Output = vir_mid::Type;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}

impl HighToMiddle for vir_high::TypeDecl {
    type Output = vir_mid::TypeDecl;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_type_decl(lowerer)?;
        self_typed.typed_to_middle_type_decl(lowerer)
    }
}

impl HighToMiddle for Vec<vir_high::Type> {
    type Output = Vec<vir_mid::Type>;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}

impl HighToMiddle for Vec<vir_high::VariableDecl> {
    type Output = Vec<vir_mid::VariableDecl>;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}

impl HighToMiddle for Vec<vir_high::Expression> {
    type Output = Vec<vir_mid::Expression>;
    fn high_to_middle(
        self,
        lowerer: &mut crate::encoder::Encoder<'_, '_>,
    ) -> SpannedEncodingResult<Self::Output> {
        let self_typed = self.high_to_typed_expression(lowerer)?;
        self_typed.typed_to_middle_expression(lowerer)
    }
}
