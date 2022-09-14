//! This module contains a custom heap encoding that can be used instead of the
//! Viper builtin heap encoding. This module depends on `ErrorManager` and,
//! therefore, has to be in the `prusti-viper` crate.

mod heap_encoder;
mod variable_declarations;

use self::heap_encoder::HeapEncoder;
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    middle::core_proof::predicates::OwnedPredicateInfo,
    mir::errors::ErrorInterface,
    Encoder,
};
use std::collections::BTreeMap;
use vir_crate::{
    common::cfg::Cfg,
    low::{self as vir_low},
};

pub(in super::super) fn custom_heap_encoding<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p mut Encoder<'v, 'tcx>,
    program: &mut vir_low::Program,
    predicate_info: BTreeMap<String, OwnedPredicateInfo>,
) -> SpannedEncodingResult<()> {
    let mut procedures = Vec::new();
    let mut heap_encoder = HeapEncoder::new(
        encoder,
        &program.predicates,
        predicate_info,
        &program.functions,
    );
    for procedure in std::mem::take(&mut program.procedures) {
        heap_encoder.reset();
        let procedure = custom_heap_encoding_for_procedure(&mut heap_encoder, procedure)?;
        procedures.push(procedure);
    }
    program.procedures = procedures;
    program
        .domains
        .extend(heap_encoder.generate_necessary_domains()?);
    Ok(())
}

fn custom_heap_encoding_for_procedure<'p, 'v: 'p, 'tcx: 'v>(
    heap_encoder: &mut HeapEncoder<'p, 'v, 'tcx>,
    mut procedure: vir_low::ProcedureDecl,
) -> SpannedEncodingResult<vir_low::ProcedureDecl> {
    let predecessors = procedure.predecessors_owned();
    let traversal_order = procedure.get_topological_sort();
    let mut basic_block_edges = BTreeMap::new();
    for label in &traversal_order {
        heap_encoder.prepare_new_current_block(label, &predecessors, &mut basic_block_edges)?;
        let mut statements = Vec::new();
        let block = procedure.basic_blocks.get_mut(label).unwrap();
        for statement in std::mem::take(&mut block.statements) {
            heap_encoder.encode_statement(&mut statements, statement)?;
        }
        block.statements = statements;
        heap_encoder.finish_current_block(label.clone())?;
    }
    for label in traversal_order {
        if let Some(intermediate_blocks) = basic_block_edges.remove(&label) {
            let mut block = procedure.basic_blocks.remove(&label).unwrap();
            for (successor_label, equalities) in intermediate_blocks {
                let intermediate_block_label = vir_low::Label::new(format!(
                    "label__from__{}__to__{}",
                    label.name, successor_label.name
                ));
                block
                    .successor
                    .replace_label(&successor_label, intermediate_block_label.clone());
                let mut successor_statements = Vec::new();
                for (variable_name, ty, position, old_version, new_version) in equalities {
                    let new_variable =
                        heap_encoder.create_variable(&variable_name, ty.clone(), new_version)?;
                    let old_variable =
                        heap_encoder.create_variable(&variable_name, ty.clone(), old_version)?;
                    let position = heap_encoder.encoder().change_error_context(
                        // FIXME: Get a more precise span.
                        position,
                        ErrorCtxt::Unexpected,
                    );
                    let statement = vir_low::macros::stmtp! {
                        position => assume (new_variable == old_variable)
                    };
                    successor_statements.push(statement);
                }
                procedure.basic_blocks.insert(
                    intermediate_block_label,
                    vir_low::BasicBlock {
                        statements: successor_statements,
                        successor: vir_low::Successor::Goto(successor_label),
                    },
                );
            }
            procedure.basic_blocks.insert(label, block);
        }
    }
    let init_permissions_to_zero =
        heap_encoder.generate_init_permissions_to_zero(procedure.position)?;
    procedure.locals.extend(heap_encoder.take_variables());
    procedure
        .basic_blocks
        .get_mut(&procedure.entry)
        .unwrap()
        .statements
        .splice(0..0, init_permissions_to_zero);
    Ok(procedure)
}
