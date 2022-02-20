use super::{IntoSnapshot, SnapshotsInterface};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{into_low::IntoLowInterface, lowerer::Lowerer},
};
use vir_crate::{
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

impl IntoSnapshot for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        match self {
            Self::Local(expression) => expression.create_snapshot(lowerer),
            Self::Constructor(expression) => expression.create_snapshot(lowerer),
            // Self::Variant(expression) => expression.create_snapshot(lowerer),
            Self::Field(expression) => expression.create_snapshot(lowerer),
            // Self::Deref(expression) => expression.create_snapshot(lowerer),
            // Self::AddrOf(expression) => expression.create_snapshot(lowerer),
            // Self::LabelledOld(expression) => expression.create_snapshot(lowerer),
            Self::Constant(expression) => expression.create_snapshot(lowerer),
            Self::UnaryOp(expression) => expression.create_snapshot(lowerer),
            Self::BinaryOp(expression) => expression.create_snapshot(lowerer),
            // Self::ContainerOp(expression) => expression.create_snapshot(lowerer),
            // Self::Seq(expression) => expression.create_snapshot(lowerer),
            // Self::Conditional(expression) => expression.create_snapshot(lowerer),
            // Self::Quantifier(expression) => expression.create_snapshot(lowerer),
            // Self::LetExpr(expression) => expression.create_snapshot(lowerer),
            // Self::FuncApp(expression) => expression.create_snapshot(lowerer),
            // Self::Downcast(expression) => expression.create_snapshot(lowerer),
            x => unimplemented!("{:?}", x),
        }
    }
}

impl IntoSnapshot for vir_mid::Local {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let snapshot_variable = self.variable.create_snapshot(lowerer)?;
        Ok(vir_low::Expression::local(snapshot_variable, self.position))
    }
}

impl IntoSnapshot for vir_mid::Constructor {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let mut arguments = Vec::new();
        for argument in &self.arguments {
            arguments.push(argument.create_snapshot(lowerer)?);
        }
        lowerer.encode_snapshot_constructor_base_call(&self.ty, arguments, self.position)
    }
}

impl IntoSnapshot for vir_mid::Field {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let base_snapshot = self.base.create_snapshot(lowerer)?;
        lowerer.encode_field_snapshot(
            self.base.get_type(),
            &self.field,
            base_snapshot,
            self.position,
        )
    }
}

impl IntoSnapshot for vir_mid::Constant {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let argument = lowerer.lower_expression(self.clone().into())?;
        lowerer.encode_constant_snapshot(&self.ty, argument, self.position)
    }
}

impl IntoSnapshot for vir_mid::UnaryOp {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let argument_snapshot = self.argument.create_snapshot(lowerer)?;
        lowerer.encode_unary_op_call(
            self.op_kind,
            self.get_type(),
            argument_snapshot,
            self.position,
        )
    }
}

impl IntoSnapshot for vir_mid::BinaryOp {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let left_snapshot = self.left.create_snapshot(lowerer)?;
        let right_snapshot = self.right.create_snapshot(lowerer)?;
        lowerer.encode_binary_op_call(
            self.op_kind,
            self.get_type(),
            left_snapshot,
            right_snapshot,
            self.position,
        )
    }
}
