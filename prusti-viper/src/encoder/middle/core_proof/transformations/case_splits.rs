use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::{expression::UnaryOperationHelpers, graphviz::ToGraphviz, position::Positioned},
    low::{self as vir_low},
};

pub(in super::super) fn desugar_case_splits(
    source_filename: &str,
    mut program: vir_low::Program,
) -> SpannedEncodingResult<vir_low::Program> {
    for procedure in std::mem::take(&mut program.procedures) {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_before_case_split",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
        desugar_case_splits_in_procedure(procedure, &mut program.procedures)?;
    }
    for procedure in &program.procedures {
        if prusti_common::config::dump_debug_info() {
            prusti_common::report::log::report_with_writer(
                "graphviz_method_vir_low_after_case_split",
                format!("{}.{}.dot", source_filename, procedure.name),
                |writer| procedure.to_graphviz(writer).unwrap(),
            );
        }
    }
    Ok(program)
}

fn desugar_case_splits_in_procedure(
    procedure: vir_low::ProcedureDecl,
    procedures: &mut Vec<vir_low::ProcedureDecl>,
) -> SpannedEncodingResult<()> {
    let case_splits = collect_case_splits(&procedure)?;
    if case_splits.is_empty() {
        procedures.push(procedure);
        return Ok(());
    } else {
        expand_case_splits(&procedure, &case_splits[..], procedures)?;
    }
    Ok(())
}

fn collect_case_splits(
    procedure: &vir_low::ProcedureDecl,
) -> SpannedEncodingResult<Vec<(vir_low::Label, usize)>> {
    let mut case_splits = Vec::new();
    for (label, block) in &procedure.basic_blocks {
        for (index, statement) in block.statements.iter().enumerate() {
            if let vir_low::Statement::CaseSplit { .. } = statement {
                case_splits.push((label.clone(), index));
            }
        }
    }
    Ok(case_splits)
}

fn expand_case_splits(
    procedure: &vir_low::ProcedureDecl,
    case_splits: &[(vir_low::Label, usize)],
    procedures: &mut Vec<vir_low::ProcedureDecl>,
) -> SpannedEncodingResult<()> {
    assert!(case_splits.len() < 64);
    let number_of_choices = 1u64 << case_splits.len();
    for choices in 0..number_of_choices {
        let mut new_procedure = procedure.clone();
        new_procedure.name = format!("{}_case_split_{}", procedure.name, choices);
        let mut choice_statements =
            vec![vir_low::Statement::comment("Start case splits".to_string())];
        for (choice_location, (label, statement_index)) in case_splits.iter().enumerate() {
            let choice = (choices >> choice_location) & 1;
            let choice = choice == 1;
            let block = new_procedure.basic_blocks.get_mut(label).unwrap();
            let statement = &mut block.statements[*statement_index];
            let vir_low::Statement::CaseSplit(case_split) = statement else {
                unreachable!();
            };
            if choice {
                *statement =
                    vir_low::Statement::assume(case_split.expression.clone(), case_split.position);
            } else {
                *statement = vir_low::Statement::assume(
                    vir_low::Expression::not(case_split.expression.clone()),
                    case_split.position,
                );
            }
            choice_statements.push(statement.clone());
        }
        choice_statements.push(vir_low::Statement::comment("End case splits".to_string()));
        let entry_block = new_procedure
            .basic_blocks
            .get_mut(&new_procedure.entry)
            .unwrap();
        entry_block.statements.splice(0..0, choice_statements);
        procedures.push(new_procedure);
    }
    Ok(())
}
