use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            expression_interner::ExpressionInterner,
            procedure_executor::constraints::{BlockConstraints, ConstraintsMergeReport},
            program_context::ProgramContext,
        },
    },
};
use log::debug;
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::low::{self as vir_low, operations::ty::Typed};

pub(super) fn matches_arguments(
    arguments1: &[vir_low::Expression],
    arguments2: &[vir_low::Expression],
    constraints: &mut BlockConstraints,
    expression_interner: &mut ExpressionInterner,
    program_context: &ProgramContext<impl EncoderContext>,
) -> SpannedEncodingResult<bool> {
    debug_assert_eq!(arguments1.len(), arguments2.len());
    for (arg1, arg2) in arguments1.iter().zip(arguments2) {
        if !constraints.is_equal(expression_interner, program_context, arg1, arg2)? {
            debug!("arguments do not match: {} != {}", arg1, arg2);
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn matches_arguments_with_remaps(
    self_arguments: &[vir_low::Expression],
    other_arguments: &[vir_low::Expression],
    constraints_merge_report: &ConstraintsMergeReport,
    constraints: &mut BlockConstraints,
    expression_interner: &mut ExpressionInterner,
    program_context: &ProgramContext<impl EncoderContext>,
) -> SpannedEncodingResult<bool> {
    debug_assert_eq!(self_arguments.len(), other_arguments.len());
    let other_remaps = constraints_merge_report.get_other_remaps();
    let dropped_self_equalities = constraints_merge_report.get_dropped_self_equalities();
    let dropped_other_equalities = constraints_merge_report.get_dropped_other_equalities();
    // We use `remap_targets` to ensure that we are not remapping back and
    // forth.
    let mut remap_targets = FxHashSet::default();
    for (self_arg, other_arg) in self_arguments.iter().zip(other_arguments) {
        // `self_arg` was already remaped in the caller.
        let remap_self = self_arg.clone();
        let remap_other = other_arg.clone().map_variables(|variable| {
            if let Some(remap) = other_remaps.get(&variable) {
                remap_targets.insert(remap.name.clone());
                remap.clone()
            } else {
                variable
            }
        });
        let remap_self = remap_self.map_variables(|variable| {
            if let Some(remap) = dropped_self_equalities.get(&variable) {
                if remap_targets.contains(&variable.name) {
                    // We are remapping back and forth.
                    variable
                } else {
                    remap_targets.insert(remap.name.clone());
                    remap.clone()
                }
            } else {
                variable
            }
        });
        let remap_other = remap_other.map_variables(|variable| {
            if let Some(remap) = dropped_other_equalities.get(&variable) {
                if remap_targets.contains(&variable.name) {
                    // We are remapping back and forth.
                    variable
                } else {
                    remap_targets.insert(remap.name.clone());
                    remap.clone()
                }
            } else {
                variable
            }
        });
        if !constraints.is_equal(
            expression_interner,
            program_context,
            &remap_self,
            &remap_other,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

// pub(super) fn is_place_non_aliased(place: &vir_low::Expression) -> bool {
//     assert_eq!(place.get_type(), &vir_low::macros::ty!(PlaceOption));
//     match place {
//         vir_low::Expression::DomainFuncApp(domain_func_app)
//             if domain_func_app.arguments.len() == 1 =>
//         {
//             let argument = &domain_func_app.arguments[0];
//             if domain_func_app.function_name == "place_option_some" {
//                 true
//             } else {
//                 is_place_non_aliased(argument)
//             }
//         }
//         vir_low::Expression::DomainFuncApp(domain_func_app) => {
//             assert_eq!(domain_func_app.function_name, "place_option_none");
//             false
//         }
//         vir_low::Expression::LabelledOld(labelled_old) => is_place_non_aliased(&labelled_old.base),
//         _ => unreachable!("place: {place}"),
//     }
// }
