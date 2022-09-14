// use super::super::utils::matches_arguments;
// use crate::encoder::{
//     errors::{SpannedEncodingError, SpannedEncodingResult},
//     middle::core_proof::transformations::{
//         encoder_context::EncoderContext,
//         symbolic_execution::utils::all_heap_independent,
//         symbolic_execution_new::{
//             expression_interner::ExpressionInterner,
//             procedure_executor::constraints::{BlockConstraints, MergeReport},
//             program_context::ProgramContext,
//         },
//     },
// };
// use log::debug;
// use std::collections::BTreeMap;
// use vir_crate::{
//     common::display,
//     low::{
//         self as vir_low,
//         expression::visitors::{ExpressionFallibleFolder, ExpressionWalker},
//     },
// };

// #[derive(Default, Clone)]
// pub(in super::super) struct PredicateSnapshots {
//     /// Maps predicate name to a list of predicate instances.
//     snapshots: BTreeMap<String, Vec<PredicateSnapshot>>,
// }

// impl std::fmt::Display for PredicateSnapshots {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         for (predicate_name, snapshots) in &self.snapshots {
//             writeln!(f, "{}:", predicate_name)?;
//             for snapshot in snapshots {
//                 writeln!(f, "  {}", snapshot)?;
//             }
//         }
//         Ok(())
//     }
// }

// #[derive(Default)]
// pub(in super::super::super) struct GlobalPredicateSnapshotState {
//     pub(super) snapshots_at_label: BTreeMap<String, PredicateSnapshots>,
//     variables: Vec<vir_low::VariableDecl>,
// }

// #[derive(Clone)]
// struct PredicateSnapshot {
//     /// Predicate arguments.
//     arguments: Vec<vir_low::Expression>,
//     /// The current snapshot of the predicate.
//     snapshot: vir_low::VariableDecl,
// }

// impl std::fmt::Display for PredicateSnapshot {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "{}: {}", display::cjoin(&self.arguments), self.snapshot)?;
//         Ok(())
//     }
// }

// impl GlobalPredicateSnapshotState {
//     pub(in super::super) fn insert(
//         &mut self,
//         label: String,
//         snapshots: &PredicateSnapshots,
//     ) -> SpannedEncodingResult<()> {
//         assert!(self
//             .snapshots_at_label
//             .insert(label, snapshots.clone())
//             .is_none());
//         Ok(())
//     }

//     pub(in super::super::super) fn take_variables(&mut self) -> Vec<vir_low::VariableDecl> {
//         std::mem::take(&mut self.variables)
//     }
// }

// impl PredicateSnapshots {
//     pub(in super::super) fn create_predicate_snapshot(
//         &mut self,
//         program_context: &ProgramContext<impl EncoderContext>,
//         state: &mut GlobalPredicateSnapshotState,
//         predicate_name: &str,
//         arguments: Vec<vir_low::Expression>,
//     ) -> SpannedEncodingResult<Option<vir_low::VariableDecl>> {
//         let predicate_snapshots = self
//             .snapshots
//             .entry(predicate_name.to_string())
//             .or_default();
//         let snapshot_variable_name = format!(
//             "snapshot_non_aliased${}${}",
//             predicate_name,
//             state.variables.len()
//         );
//         if let Some(ty) = program_context.get_snapshot_type(predicate_name) {
//             assert!(
//                 all_heap_independent(&arguments),
//                 "arguments: {}",
//                 display::cjoin(&arguments)
//             );
//             let snapshot = vir_low::VariableDecl::new(snapshot_variable_name.clone(), ty);
//             predicate_snapshots.push(PredicateSnapshot {
//                 arguments,
//                 snapshot: snapshot.clone(),
//             });
//             state.variables.push(snapshot.clone());
//             Ok(Some(snapshot))
//         } else {
//             Ok(None)
//         }
//     }

//     pub(in super::super) fn remove_predicate_snapshot(
//         &mut self,
//         predicate_name: &str,
//         arguments: &[vir_low::Expression],
//     ) -> SpannedEncodingResult<()> {
//         let predicate_snapshots = self.snapshots.get_mut(predicate_name).unwrap();
//         for (i, predicate_snapshot) in predicate_snapshots.iter().enumerate() {
//             if arguments == &predicate_snapshot.arguments {
//                 predicate_snapshots.remove(i);
//                 return Ok(());
//             }
//         }
//         unreachable!("{predicate_name}({})", display::cjoin(arguments))
//     }

//     pub(super) fn find_snapshot(
//         &self,
//         predicate_name: &str,
//         arguments: &[vir_low::Expression],
//         constraints: &BlockConstraints,
//         expression_interner: &mut ExpressionInterner,
//         program_context: &ProgramContext<impl EncoderContext>,
//     ) -> SpannedEncodingResult<Option<vir_low::VariableDecl>> {
//         if let Some(predicate_snapshots) = self.snapshots.get(predicate_name) {
//             for predicate_snapshot in predicate_snapshots {
//                 if predicate_snapshot.matches_arguments(
//                     arguments,
//                     constraints,
//                     expression_interner,
//                     program_context,
//                 )? {
//                     return Ok(Some(predicate_snapshot.snapshot.clone()));
//                 }
//             }
//         }
//         Ok(None)
//     }

//     pub(in super::super) fn merge(
//         &mut self,
//         other: &Self,
//         constraints_merge_report: &MergeReport,
//     ) -> SpannedEncodingResult<()> {
//         unimplemented!();
//     }
// }

// impl PredicateSnapshot {
//     fn matches_arguments(
//         &self,
//         arguments: &[vir_low::Expression],
//         constraints: &BlockConstraints,
//         expression_interner: &mut ExpressionInterner,
//         program_context: &ProgramContext<impl EncoderContext>,
//     ) -> SpannedEncodingResult<bool> {
//         matches_arguments(
//             &self.arguments,
//             arguments,
//             constraints,
//             expression_interner,
//             program_context,
//         )
//         // debug_assert_eq!(self.arguments.len(), arguments.len());
//         // for (arg1, arg2) in self.arguments.iter().zip(arguments) {
//         //     if !constraints.is_equal(expression_interner, program_context, arg1, arg2)? {
//         //         return Ok(false);
//         //     }
//         // }
//         // Ok(true)
//     }
// }
