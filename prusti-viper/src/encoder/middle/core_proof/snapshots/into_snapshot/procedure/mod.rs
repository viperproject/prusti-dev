//! Code for encoding expressions into snapshots in non-pure contexts such as
//! procedure bodies. Most important difference from `pure` is that this
//! encoding uses SSA.

use super::common::IntoSnapshotLowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        lowerer::{FunctionsLowererInterface, Lowerer},
        references::ReferencesInterface,
        snapshots::SnapshotVariablesInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

mod traits;

pub(in super::super::super) use self::traits::{
    IntoProcedureBoolExpression, IntoProcedureFinalSnapshot, IntoProcedureSnapshot,
};

#[derive(Default)]
struct ProcedureSnapshot {
    old_label: Option<String>,
    deref_to_final: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for ProcedureSnapshot {
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        if let Some(label) = &self.old_label {
            lowerer.snapshot_variable_version_at_label(variable, label)
        } else {
            lowerer.current_snapshot_variable_version(variable)
        }
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_procedure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::FuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let parent_old_label = std::mem::replace(&mut self.old_label, Some(old.label.clone()));
        let result = self.expression_to_snapshot(lowerer, &old.base, expect_math_bool);
        self.old_label = parent_old_label;
        result
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = if self.deref_to_final {
            self.deref_to_final = false;
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            self.deref_to_final = true;
            lowerer.reference_target_final_snapshot(
                deref.base.get_type(),
                base_snapshot,
                Default::default(),
            )?
        } else {
            let base_snapshot =
                self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
            lowerer.reference_target_current_snapshot(
                deref.base.get_type(),
                base_snapshot,
                Default::default(),
            )?
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }
}
