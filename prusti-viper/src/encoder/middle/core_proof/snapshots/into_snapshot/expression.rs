use super::IntoSnapshot;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        into_low::IntoLowInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        snapshots::SnapshotValuesInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
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
            Self::Variant(expression) => expression.create_snapshot(lowerer),
            Self::Field(expression) => expression.create_snapshot(lowerer),
            // Self::Deref(expression) => expression.create_snapshot(lowerer),
            // Self::AddrOf(expression) => expression.create_snapshot(lowerer),
            // Self::LabelledOld(expression) => expression.create_snapshot(lowerer),
            Self::Constant(expression) => expression.create_snapshot(lowerer),
            Self::UnaryOp(expression) => expression.create_snapshot(lowerer),
            Self::BinaryOp(expression) => expression.create_snapshot(lowerer),
            // Self::ContainerOp(expression) => expression.create_snapshot(lowerer),
            // Self::Seq(expression) => expression.create_snapshot(lowerer),
            Self::Conditional(expression) => expression.create_snapshot(lowerer),
            // Self::Quantifier(expression) => expression.create_snapshot(lowerer),
            // Self::LetExpr(expression) => expression.create_snapshot(lowerer),
            Self::FuncApp(expression) => expression.create_snapshot(lowerer),
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
        lowerer.construct_struct_snapshot(&self.ty, arguments, self.position)
    }
}

impl IntoSnapshot for vir_mid::Variant {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let base_snapshot = self.base.create_snapshot(lowerer)?;
        lowerer.obtain_enum_variant_snapshot(
            self.base.get_type(),
            &self.variant_index,
            base_snapshot,
            self.position,
        )
    }
}

impl IntoSnapshot for vir_mid::Field {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let base_snapshot = self.base.create_snapshot(lowerer)?;
        if self.field.is_discriminant() {
            let ty = self.base.get_type();
            // FIXME: Create a method for obtainging the discriminant type.
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            let enum_decl = type_decl.unwrap_enum();
            let discriminant_call =
                lowerer.obtain_enum_discriminant(base_snapshot, ty, Default::default())?;
            lowerer.construct_constant_snapshot(
                &enum_decl.discriminant_type,
                discriminant_call,
                self.position,
            )
        } else {
            lowerer.obtain_struct_field_snapshot(
                self.base.get_type(),
                &self.field,
                base_snapshot,
                self.position,
            )
        }
    }
}

impl IntoSnapshot for vir_mid::Constant {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let argument = lowerer.lower_expression(self.clone().into())?;
        lowerer.construct_constant_snapshot(&self.ty, argument, self.position)
    }
}

impl IntoSnapshot for vir_mid::UnaryOp {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let argument_snapshot = self.argument.create_snapshot(lowerer)?;
        lowerer.construct_unary_op_snapshot(
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
        let arg_type = self.left.get_type();
        assert_eq!(arg_type, self.right.get_type());
        lowerer.construct_binary_op_snapshot(
            self.op_kind,
            self.get_type(),
            arg_type,
            left_snapshot,
            right_snapshot,
            self.position,
        )
    }
}

impl IntoSnapshot for vir_mid::Conditional {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let guard_snapshot = lowerer.lower_expression_into_snapshot_constant_value(&self.guard)?;
        let then_expr_snapshot = self.then_expr.create_snapshot(lowerer)?;
        let else_expr_snapshot = self.else_expr.create_snapshot(lowerer)?;
        let arg_type = self.then_expr.get_type();
        assert_eq!(arg_type, self.else_expr.get_type());
        Ok(vir_low::Expression::conditional(
            guard_snapshot,
            then_expr_snapshot,
            else_expr_snapshot,
            self.position,
        ))
    }
}

impl IntoSnapshot for vir_mid::FuncApp {
    type Target = vir_low::Expression;
    fn create_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    ) -> SpannedEncodingResult<Self::Target> {
        let arguments = self.arguments.create_snapshot(lowerer)?;
        let return_type = self.return_type.create_snapshot(lowerer)?;
        let func_app = lowerer.create_func_app(
            self.get_identifier(),
            arguments,
            return_type,
            self.position,
        )?;
        Ok(vir_low::Expression::FuncApp(func_app))
    }
}
