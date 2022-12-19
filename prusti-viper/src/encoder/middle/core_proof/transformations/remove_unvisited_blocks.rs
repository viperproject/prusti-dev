use crate::encoder::errors::SpannedEncodingResult;
use rustc_hash::FxHashMap;
use vir_crate::{
    common::position::Positioned,
    low::{self as vir_low},
};

pub(in super::super) fn remove_unvisited_blocks(
    procedures: &mut Vec<vir_low::ProcedureDecl>,
    label_markers: &FxHashMap<String, bool>,
) -> SpannedEncodingResult<()> {
    for procedure in procedures {
        for (label, block) in &mut procedure.basic_blocks {
            if !label_markers.get(&label.name).unwrap_or(&true) {
                // The block was not visited. Replace with assume false.
                let mut position = None;
                for statement in &block.statements {
                    let statement_position = statement.position();
                    if !statement_position.is_default() {
                        position = Some(statement_position);
                        break;
                    }
                }
                if let Some(position) = position {
                    block.statements = vec![vir_low::Statement::assume(false.into(), position)];
                }
            }
        }
    }
    Ok(())
}
