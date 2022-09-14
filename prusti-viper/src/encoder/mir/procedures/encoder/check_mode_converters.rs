use super::ProcedureEncoder;
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    mir::{specifications::SpecificationsInterface, types::MirTypeEncoderInterface},
    Encoder,
};

use vir_crate::{
    common::{
        check_mode::CheckMode,
        expression::{BinaryOperationHelpers, ExpressionIterator},
        position::Positioned,
    },
    high::{self as vir_high, operations::ty::Typed},
};

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    /// Convert expression to the one usable for the current check mode:
    ///
    /// * For `Both` and `Specifications`: keep the expression unchanged.
    /// * For `CoreProof` keep only the raw pointer dereferences because we need
    ///   to check that they are framed.
    ///
    /// If `disallow_permissions` is true, then checks that the expression does
    /// not contain accesibility predicates.
    pub(super) fn convert_expression_to_check_mode(
        &mut self,
        expression: vir_high::Expression,
        disallow_permissions: bool,
        allow_specs_in_memory_safety: bool,
        _framing_variables: &[vir_high::VariableDecl],
    ) -> SpannedEncodingResult<Option<vir_high::Expression>> {
        if disallow_permissions && !expression.is_pure() {
            let span = self
                .encoder
                .error_manager()
                .position_manager()
                .get_span(expression.position().into())
                .cloned()
                .unwrap();
            return Err(SpannedEncodingError::incorrect(
                "only unsafe functions can use permissions in their contracts",
                span,
            ));
        }
        match self.check_mode {
            CheckMode::MemorySafety => {
                // Unsafe functions are checked with `CheckMode::UnsafeSafety`. For all
                // other functions it is forbidden to have accessibility
                // predicates in their contracts.
                assert!(disallow_permissions);
                // Framing will be checked with `CheckMode::MemorySafetyWithFunctional`.
                if allow_specs_in_memory_safety {
                    Ok(Some(expression))
                } else {
                    Ok(None)
                }
            }
            CheckMode::MemorySafetyWithFunctional => {
                // Unsafe functions are checked with `CheckMode::UnsafeSafety`. For all
                // other functions it is forbidden to have accessibility
                // predicates in their contracts.
                assert!(disallow_permissions);
                // Framing is checked automatically by the encoding.
                Ok(Some(expression))
            }
            CheckMode::PurificationFunctional => {
                unreachable!("outdated code");
                // // Unsafe functions are checked with `CheckMode::UnsafeSafety`. For all
                // // other functions it is forbidden to have accessibility
                // // predicates in their contracts.
                // assert!(disallow_permissions);
                // Ok(Some(expression))
            }
            CheckMode::PurificationSoudness => {
                unreachable!("outdated code");
                // // Check comment for `CheckMode::PurificationFunctional`.
                // assert!(disallow_permissions);
                // // Even though we forbid accessibility predicates in safe
                // // functions, we may still have raw pointers in specifications
                // // that are framed by type invariants.
                // let dereferenced_places = expression.collect_guarded_dereferenced_places();
                // if dereferenced_places.is_empty() {
                //     Ok(None)
                // } else {
                //     let framing_places: Vec<vir_high::Expression> = framing_variables
                //         .iter()
                //         .map(|var| var.clone().into())
                //         .collect();
                //     let check = construct_framing_assertion(
                //         self.encoder,
                //         dereferenced_places,
                //         &framing_places,
                //     )?;
                //     Ok(Some(check))
                // }
            }
            CheckMode::UnsafeSafety => {
                // Framing is checked automatically by the encoding.
                Ok(Some(expression))
            }
        }
    }

    pub(super) fn convert_expression_to_check_mode_call_site(
        &mut self,
        expression: vir_high::Expression,
        is_unsafe: bool,
        is_checked: bool,
        _framing_arguments: &[vir_high::Expression],
    ) -> SpannedEncodingResult<Option<vir_high::Expression>> {
        match self.check_mode {
            CheckMode::MemorySafety => {
                if is_unsafe || is_checked {
                    // We are calling an unsafe function from a safe one.
                    Ok(Some(expression))
                } else {
                    Ok(None)
                }
            }
            CheckMode::MemorySafetyWithFunctional
            | CheckMode::PurificationFunctional
            | CheckMode::UnsafeSafety => Ok(Some(expression)),
            CheckMode::PurificationSoudness => {
                unimplemented!();
                // let dereferenced_places = expression.collect_guarded_dereferenced_places();
                // let check = if dereferenced_places.is_empty() {
                //     if is_unsafe {
                //         Some(expression)
                //     } else {
                //         None
                //     }
                // } else {
                //     let check = construct_framing_assertion(
                //         self.encoder,
                //         dereferenced_places,
                //         framing_arguments,
                //     )?;
                //     if is_unsafe {
                //         Some(vir_high::Expression::and(expression, check))
                //     } else {
                //         Some(check)
                //     }
                // };
                // Ok(check)
            }
        }
    }
}

fn construct_framing_assertion(
    encoder: &mut Encoder,
    dereferenced_places: Vec<(vir_high::Expression, vir_high::Expression)>,
    framing_places: &[vir_high::Expression],
) -> SpannedEncodingResult<vir_high::Expression> {
    let type_invariant_framing_places =
        construct_type_invariant_framing_places(encoder, framing_places)?;
    let mut type_invariant_framed_places = Vec::new();
    for (guard, place) in dereferenced_places {
        if is_framed(&place, &type_invariant_framing_places) {
            let function = vir_high::Expression::builtin_func_app(
                vir_high::BuiltinFunc::EnsureOwnedPredicate,
                Vec::new(),
                vec![place.clone()],
                vir_high::Type::Bool,
                place.position(),
            );
            let check = vir_high::Expression::implies(guard, function);
            type_invariant_framed_places.push(check);
        } else {
            unimplemented!("Outdated code.");
            // let span = encoder
            //     .error_manager()
            //     .position_manager()
            //     .get_span(place.position().into())
            //     .cloned()
            //     .unwrap();
            // return Err(SpannedEncodingError::incorrect(
            //     "the place must be framed by permissions",
            //     span,
            // ));
        }
    }
    Ok(type_invariant_framed_places.into_iter().conjoin())
}

fn construct_type_invariant_framing_places(
    encoder: &mut Encoder,
    framing_places: &[vir_high::Expression],
) -> SpannedEncodingResult<Vec<vir_high::Expression>> {
    let type_invariant_framing_places = Vec::new();
    for framing_place in framing_places {
        if framing_place.get_type().is_struct() {
            let type_decl = encoder
                .encode_type_def_high(framing_place.get_type(), true)?
                .unwrap_struct();
            if let Some(invariants) = type_decl.structural_invariant {
                for expression in invariants {
                    let _expression = expression.replace_self(framing_place);
                    unimplemented!("Outdated code?");
                    // type_invariant_framing_places.extend(expression.collect_owned_places());
                }
            }
        }
    }
    Ok(type_invariant_framing_places)
}

fn is_framed(
    place: &vir_high::Expression,
    type_invariant_framing_places: &[vir_high::Expression],
) -> bool {
    for framing_place in type_invariant_framing_places {
        if is_framed_rec(framing_place, place, type_invariant_framing_places) {
            return true;
        }
    }
    false
}

fn is_framed_rec(
    framing_place: &vir_high::Expression,
    place: &vir_high::Expression,
    type_invariant_framing_places: &[vir_high::Expression],
) -> bool {
    if framing_place == place {
        if let Some(pointer_place) = place.get_last_dereferenced_pointer() {
            is_framed(pointer_place, type_invariant_framing_places)
        } else {
            true
        }
    } else if place.is_deref() {
        false
    } else if let Some(parent) = place.get_parent_ref() {
        is_framed_rec(framing_place, parent, type_invariant_framing_places)
    } else {
        true
    }
}
