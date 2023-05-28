use super::predicate_instance::{PredicateInstance, SnapshotType};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::utils::all_heap_independent,
        symbolic_execution_new::{
            block_builder::BlockBuilder,
            egg::ExpressionEGraph,
            expression_interner::ExpressionInterner,
            procedure_executor::{
                constraints::{BlockConstraints, ConstraintsMergeReport},
                heap::{
                    utils::{matches_arguments, matches_arguments_with_remaps},
                    GlobalHeapState, HeapMergeReport,
                },
            },
            program_context::ProgramContext,
        },
    },
};
use prusti_common::config;
use vir_crate::{
    common::{
        display,
        expression::{BinaryOperationHelpers, ExpressionIterator},
    },
    low::{self as vir_low},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum MatchesResult {
    /// The two instances match and we managed to discharge all proof obligations.
    MatchesUnonditionally,
    /// The two instances match, but we could not discharge all proof
    /// obligations.
    MatchesConditionally {
        /// The assertion to be checked by the verified because we could not prove it syntactically.
        assert: vir_low::Expression,
    },
    /// The two instances do not match.
    DoesNotMatch,
}

pub(super) fn is_non_aliased(
    predicate_name: &str,
    arguments: &[vir_low::Expression],
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
) -> SpannedEncodingResult<bool> {
    if program_context.is_predicate_kind_non_aliased(predicate_name) {
        return Ok(true);
    }
    // FIXME: use program_context.
    if predicate_name.starts_with("view_shift$end$borrow$") {
        unimplemented!();
    }
    // fn construct_predicate_address_non_aliased_call(
    //     predicate_address: &vir_low::Expression,
    // ) -> vir_low::Expression {
    //     use vir_low::macros::*;
    //     let address_is_non_aliased = ty!(Bool);
    //     expr! {
    //         (ComputeAddress::address_is_non_aliased([predicate_address.clone()]))
    //     }
    // }
    match program_context.get_predicate_kind(predicate_name) {
        vir_low::PredicateKind::MemoryBlock => {
            let predicate_address = &arguments[0];
            if program_context.is_address_non_aliased(predicate_address) {
                return Ok(true);
            }
            // let predicate_address_non_aliased_call =
            //     construct_predicate_address_non_aliased_call(predicate_address);
            // if constraints.is_non_aliased_address(&predicate_address_non_aliased_call)? {
            //     eprintln!(
            //         "is_non_aliased_address: {}",
            //         predicate_address_non_aliased_call
            //     );
            //     return Ok(true);
            // }
            // eprintln!("aliased_address: {}", predicate_address_non_aliased_call);
            // if solver.is_true(&predicate_address_non_aliased_call)? {
            //     return Ok(true);
            // } else {
            //     solver.saturate()?;
            //     if solver.is_true(&predicate_address_non_aliased_call)? {
            //         return Ok(true);
            //     }
            // }
        }
        vir_low::PredicateKind::Owned => {
            let predicate_place = &arguments[0];
            if program_context.is_place_non_aliased(predicate_place) {
                return Ok(true);
            }
        }
        _ => {}
    }
    Ok(false)
}

pub(super) fn matches_non_aliased_diff(
    predicate_name: &str,
    predicate_arguments: &[vir_low::Expression],
    predicate_instance_arguments: &[vir_low::Expression],
    expression_interner: &mut ExpressionInterner,
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
) -> SpannedEncodingResult<(bool, Vec<(vir_low::Expression, vir_low::Expression)>)> {
    fn construct_result(
        predicate_arguments: &[vir_low::Expression],
        predicate_instance_arguments: &[vir_low::Expression],
        are_equal: bool,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        constraints: &mut BlockConstraints,
    ) -> SpannedEncodingResult<(bool, Vec<(vir_low::Expression, vir_low::Expression)>)> {
        if are_equal {
            assert_eq!(
                predicate_arguments.len(),
                predicate_instance_arguments.len()
            );
            let mut disequalities = Vec::new();
            for (left, right) in predicate_arguments
                .iter()
                .zip(predicate_instance_arguments.iter())
            {
                if !constraints.is_equal(expression_interner, program_context, left, right)? {
                    disequalities.push((left.clone(), right.clone()));
                }
            }
            Ok((true, disequalities))
        } else {
            Ok((false, Vec::new()))
        }
    }
    match program_context.get_predicate_kind(predicate_name) {
        vir_low::PredicateKind::Owned => construct_result(
            predicate_arguments,
            predicate_instance_arguments,
            predicate_arguments[0] == predicate_instance_arguments[0],
            expression_interner,
            program_context,
            constraints,
        ),
        vir_low::PredicateKind::MemoryBlock => {
            // We need to include the size because after splitting the memory
            // block we sometimes get a smaller memory block at the same
            // location.
            let are_equal = (predicate_arguments[0] == predicate_instance_arguments[0])
                && (predicate_arguments[1] == predicate_instance_arguments[1]);
            construct_result(
                predicate_arguments,
                predicate_instance_arguments,
                are_equal,
                expression_interner,
                program_context,
                constraints,
            )
        }
        vir_low::PredicateKind::LifetimeToken => todo!(),
        vir_low::PredicateKind::CloseFracRef => todo!(),
        // vir_low::PredicateKind::WithoutSnapshotFrac => todo!(),
        vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
        vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
            assert_eq!(predicate_name, "MemoryBlockStackDrop");
            construct_result(
                predicate_arguments,
                predicate_instance_arguments,
                predicate_arguments[0] == predicate_instance_arguments[0],
                expression_interner,
                program_context,
                constraints,
            )
        }
        vir_low::PredicateKind::DeadLifetimeToken => todo!(),
        vir_low::PredicateKind::EndBorrowViewShift => {
            let vir_low::Expression::Local(local1) = &predicate_arguments[0] else {
                unreachable!()
            };
            let vir_low::Expression::Local(local2) = &predicate_instance_arguments[0] else {
                unreachable!()
            };
            // FIXME: Do not rely on strings.
            let lifetime1 = &local1.variable.name.splitn(2, '$').nth(0).unwrap();
            let lifetime2 = &local2.variable.name.splitn(2, '$').nth(0).unwrap();
            construct_result(
                predicate_arguments,
                predicate_instance_arguments,
                lifetime1 == lifetime2,
                expression_interner,
                program_context,
                constraints,
            )
        }
    }
}

pub(super) fn matches_non_aliased(
    predicate_name: &str,
    predicate_arguments: &[vir_low::Expression],
    predicate_instance_arguments: &[vir_low::Expression],
    expression_interner: &mut ExpressionInterner,
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
) -> SpannedEncodingResult<MatchesResult> {
    let (are_equal, disequalities) = matches_non_aliased_diff(
        predicate_name,
        predicate_arguments,
        predicate_instance_arguments,
        expression_interner,
        program_context,
        constraints,
    )?;
    if are_equal {
        if disequalities.is_empty() {
            Ok(MatchesResult::MatchesUnonditionally)
        } else {
            let assert = disequalities
                .into_iter()
                .map(|(left, right)| vir_low::Expression::equals(left, right))
                .conjoin();
            Ok(MatchesResult::MatchesConditionally { assert })
        }
    } else {
        Ok(MatchesResult::DoesNotMatch)
    }
}

pub(super) fn predicate_matches_non_aliased(
    predicate: &vir_low::PredicateAccessPredicate,
    predicate_instance_arguments: &[vir_low::Expression],
    expression_interner: &mut ExpressionInterner,
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
) -> SpannedEncodingResult<MatchesResult> {
    matches_non_aliased(
        &predicate.name,
        &predicate.arguments,
        predicate_instance_arguments,
        expression_interner,
        program_context,
        constraints,
    )
}

// pub(super) fn assert_arguments_equal_non_aliased(
//     arguments1: &[vir_low::Expression],
//     arguments2: &[vir_low::Expression],
//     expression_interner: &mut ExpressionInterner,
//     program_context: &ProgramContext<impl EncoderContext>,
//     constraints: &mut BlockConstraints,
// ) -> SpannedEncodingResult<MatchesResult> {
//     assert_eq!(arguments1.len(), arguments2.len());
//     let mut disequalities = Vec::new();
//     for (left, right) in arguments1.iter().zip(arguments2.iter()) {
//         if !constraints.is_equal(expression_interner, program_context, left, right)? {
//             disequalities.push(vir_low::Expression::equals(left.clone(), right.clone()));
//         }
//     }
//     if disequalities.is_empty() {
//         Ok(MatchesResult::MatchesUnonditionally)
//     } else {
//         Ok(MatchesResult::MatchesConditionally {
//             assert: disequalities.into_iter().conjoin(),
//         })
//     }
// }

// fn assert_arguments_equal_non_aliased(
//     arguments1: &[vir_low::Expression],
//     arguments2: &[vir_low::Expression],
//     block_builder: &mut BlockBuilder,
//     position: vir_low::Position,
// ) -> SpannedEncodingResult<()> {
//     assert_eq!(arguments1.len(), arguments2.len());
//     for (left, right) in arguments1.iter().zip(arguments2.iter()) {
//         block_builder.add_statement(
//             vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
//                 left.clone(),
//                 right.clone(),
//             ))
//             .set_default_position(position),
//         )?;
//     }
//     Ok(())
// }
