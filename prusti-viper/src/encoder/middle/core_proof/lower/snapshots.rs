use crate::encoder::{middle::core_proof::MidCoreProofEncoderInterface, Encoder};
use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
    middle::{self as vir_mid, operations::ty::Typed},
};

/// Encodes the given expression into its snapshot.
pub(super) fn encode_into_snapshot<'v, 'tcx>(
    encoder: &mut Encoder<'v, 'tcx>,
    expression: &vir_mid::Expression,
) -> vir_low::Expression {
    let mut snapshot_encoder = SnapshotEncoder { encoder };
    expression.create_snapshot(&mut snapshot_encoder)
}

trait State {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression;
}

struct SnapshotEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p mut Encoder<'v, 'tcx>,
}

impl<'p, 'v, 'tcx> State for SnapshotEncoder<'p, 'v, 'tcx> {
    fn lower_expression(
        &mut self,
        expression: vir_mid::Expression,
    ) -> vir_low::ast::expression::Expression {
        self.encoder.lower_expression_into_low(expression)
    }
}

trait IntoSnapshot {
    type Target;
    fn create_snapshot<S: State>(&self, encoder: &mut S) -> Self::Target;
}

impl IntoSnapshot for vir_mid::Expression {
    type Target = vir_low::Expression;
    fn create_snapshot<S: State>(&self, encoder: &mut S) -> Self::Target {
        match self {
            Self::Local(expression) => expression.create_snapshot(encoder),
            Self::Field(expression) => expression.create_snapshot(encoder),
            Self::Constant(expression) => expression.create_snapshot(encoder),
            x => unimplemented!("{:?}", x),
        }
    }
}

impl IntoSnapshot for vir_mid::Local {
    type Target = vir_low::Expression;
    fn create_snapshot<S: State>(&self, _encoder: &mut S) -> Self::Target {
        let snapshot_variable = vir_low::VariableDecl::new(
            format!("{}$snapshot", self.variable.name),
            vir_low::Type::domain(format!("Snap${}", self.variable.ty.get_identifier())),
        );
        vir_low::Expression::local(snapshot_variable, self.position.into())
    }
}

impl IntoSnapshot for vir_mid::Field {
    type Target = vir_low::Expression;
    fn create_snapshot<S: State>(&self, encoder: &mut S) -> Self::Target {
        let function_name = format!(
            "snap_field${}${}",
            self.base.get_type().get_identifier(),
            self.field.name
        );
        let return_type = vir_low::Type::domain(format!("Snap${}", self.field.ty.get_identifier()));
        let position = self.position.into();
        let base = self.base.create_snapshot(encoder);
        let parameter = vir_low::VariableDecl::new(
            "_1",
            vir_low::operations::ty::Typed::get_type(&base).clone(),
        );
        vir_low::Expression::domain_func_app(
            format!("Snap${}", self.base.get_type().get_identifier()),
            function_name,
            vec![base],
            vec![parameter],
            return_type,
            position,
        )
    }
}

impl IntoSnapshot for vir_mid::Constant {
    type Target = vir_low::Expression;
    fn create_snapshot<S: State>(&self, encoder: &mut S) -> Self::Target {
        let function_name = format!("snap_constructor${}", self.ty.get_identifier());
        let return_type = vir_low::Type::domain(format!("Snap${}", self.ty.get_identifier()));
        let position = self.position.into();
        let arg = encoder.lower_expression(self.clone().into());
        let parameter = vir_low::VariableDecl::new(
            "_1",
            vir_low::operations::ty::Typed::get_type(&arg).clone(),
        );
        vir_low::Expression::domain_func_app(
            format!("Snap${}", self.ty.get_identifier()),
            function_name,
            vec![arg],
            vec![parameter],
            return_type,
            position,
        )
    }
}
