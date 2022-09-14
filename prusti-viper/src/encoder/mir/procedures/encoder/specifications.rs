use super::ProcedureEncoder;
use crate::{
    encoder::{
        errors::{SpannedEncodingError, SpannedEncodingResult},
        Encoder,
    },
    error_incorrect,
};
use vir_crate::high::{
    self as vir_high,
    operations::ty::Typed,
    visitors::{default_fallible_fold_labelled_old, ExpressionFallibleFolder},
};

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn desugar_pledges_in_postcondition(
        &mut self,
        precondition_label: &str,
        result: &vir_high::Expression,
        expression: vir_high::Expression,
        broken_invariant_places: &[vir_high::Expression],
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let mut rewriter = Rewriter {
            encoder: self.encoder,
            precondition_label,
            result,
            broken_invariant_places,
            current_state: CurrentState::Postcondition,
        };
        rewriter.fallible_fold_expression(expression)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum CurrentState {
    Precondition,
    Postcondition,
    AfterExpiry,
    BeforeExpiry,
}

struct Rewriter<'a, 'v, 'tcx> {
    encoder: &'a mut Encoder<'v, 'tcx>,
    precondition_label: &'a str,
    result: &'a vir_high::Expression,
    broken_invariant_places: &'a [vir_high::Expression],
    current_state: CurrentState,
}

impl<'a, 'v, 'tcx> ExpressionFallibleFolder for Rewriter<'a, 'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn fallible_fold_labelled_old(
        &mut self,
        labelled_old: vir_high::LabelledOld,
    ) -> Result<vir_high::LabelledOld, Self::Error> {
        let old_state = self.current_state;
        if labelled_old.label == self.precondition_label {
            self.current_state = CurrentState::Precondition;
        }
        let labelled_old = default_fallible_fold_labelled_old(self, labelled_old)?;
        self.current_state = old_state;
        Ok(labelled_old)
    }

    fn fallible_fold_builtin_func_app_enum(
        &mut self,
        mut builtin_func_app: vir_high::BuiltinFuncApp,
    ) -> Result<vir_high::Expression, Self::Error> {
        let old_state = self.current_state;
        let expression = match builtin_func_app.function {
            vir_high::BuiltinFunc::AfterExpiry => {
                assert!(builtin_func_app.arguments.len() == 1);
                self.current_state = CurrentState::AfterExpiry;
                let expression = builtin_func_app.arguments.pop().unwrap();
                self.fallible_fold_expression(expression)?
            }
            vir_high::BuiltinFunc::BeforeExpiry => {
                assert!(builtin_func_app.arguments.len() == 1);
                self.current_state = CurrentState::BeforeExpiry;
                let expression = builtin_func_app.arguments.pop().unwrap();
                self.fallible_fold_expression(expression)?
            }
            _ => vir_high::Expression::BuiltinFuncApp(
                self.fallible_fold_builtin_func_app(builtin_func_app)?,
            ),
        };
        self.current_state = old_state;
        Ok(expression)
    }

    fn fallible_fold_deref_enum(
        &mut self,
        deref: vir_high::Deref,
    ) -> Result<vir_high::Expression, Self::Error> {
        let deref = self.fallible_fold_deref(deref)?;
        let expression = if deref.base.get_type().is_unique_reference() {
            match self.current_state {
                CurrentState::Precondition => {
                    if deref.base.has_prefix(self.result) {
                        let span = self
                            .encoder
                            .error_manager()
                            .position_manager()
                            .get_span(deref.position.into())
                            .unwrap()
                            .clone();
                        error_incorrect!(span => "Function result cannot be dereferenced in precondition state");
                    } else {
                        vir_high::Expression::Deref(deref)
                    }
                }
                CurrentState::Postcondition => {
                    if deref.base.has_prefix(self.result)
                        || self.broken_invariant_places.iter().any(|place| {
                            assert!(place.is_local(), "unimplemented");
                            deref.base.get_base() == place.get_base()
                        })
                    {
                        vir_high::Expression::Deref(deref)
                    } else {
                        vir_high::Expression::final_(*deref.base, deref.ty, deref.position)
                    }
                }
                CurrentState::AfterExpiry | CurrentState::BeforeExpiry => {
                    vir_high::Expression::final_(*deref.base, deref.ty, deref.position)
                }
            }
        } else {
            vir_high::Expression::Deref(deref)
        };
        Ok(expression)
    }
}
