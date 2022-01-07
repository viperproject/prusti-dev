use std::collections::BTreeMap;

use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use rustc_hir::def_id::DefId;
use vir_crate::{
    high as vir_high,
    middle::{
        self as vir_mid,
        operations::{ToMiddleExpression, ToMiddleStatement},
    },
};

pub(super) fn infer_shape_operations<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    procedure: vir_high::ProcedureDecl,
) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
    let mut state = State {
        encoder,
        _proc_def_id: proc_def_id,
    };
    state.infer_procedure(procedure)
}

struct State<'p, 'v, 'tcx> {
    encoder: &'p Encoder<'v, 'tcx>,
    _proc_def_id: DefId,
}

impl<'p, 'v, 'tcx> State<'p, 'v, 'tcx> {
    fn infer_procedure(
        &mut self,
        mut procedure: vir_high::ProcedureDecl,
    ) -> SpannedEncodingResult<vir_mid::ProcedureDecl> {
        let mut basic_blocks: BTreeMap<_, _> = procedure
            .basic_blocks
            .iter()
            .map(|(label, block)| {
                (
                    self.lower_label(label),
                    vir_mid::BasicBlock {
                        statements: Vec::new(),
                        successor: self.lower_successor(&block.successor),
                    },
                )
            })
            .collect();
        for old_label in procedure.get_topological_sort() {
            let old_block = procedure.basic_blocks.remove(&old_label).unwrap();
            let new_label = self.lower_label(&old_label);
            let new_block = basic_blocks.get_mut(&new_label).unwrap();
            self.lower_block(old_label, old_block, new_label, new_block)?;
        }
        let new_procedure = vir_mid::ProcedureDecl {
            name: procedure.name,
            entry: self.lower_label(&procedure.entry),
            basic_blocks,
        };
        Ok(new_procedure)
    }

    fn lower_successor(&self, successor: &vir_high::Successor) -> vir_mid::Successor {
        match successor {
            vir_high::Successor::Return => vir_mid::Successor::Return,
            vir_high::Successor::Goto(target) => vir_mid::Successor::Goto(self.lower_label(target)),
            vir_high::Successor::GotoSwitch(targets) => vir_mid::Successor::GotoSwitch(
                targets
                    .iter()
                    .map(|(test, target)| {
                        (
                            test.clone().to_middle_expression(self.encoder),
                            self.lower_label(target),
                        )
                    })
                    .collect(),
            ),
        }
    }

    fn lower_label(&self, label: &vir_high::BasicBlockId) -> vir_mid::BasicBlockId {
        vir_mid::BasicBlockId {
            name: label.name.clone(),
        }
    }

    fn lower_block(
        &self,
        _old_label: vir_high::BasicBlockId,
        old_block: vir_high::BasicBlock,
        _new_label: vir_mid::BasicBlockId,
        new_block: &mut vir_mid::BasicBlock,
    ) -> SpannedEncodingResult<()> {
        for statement in old_block.statements {
            self.lower_statement(statement, new_block)?;
        }
        Ok(())
    }

    fn lower_statement(
        &self,
        statement: vir_high::Statement,
        new_block: &mut vir_mid::BasicBlock,
    ) -> SpannedEncodingResult<()> {
        new_block
            .statements
            .push(statement.to_middle_statement(self.encoder));
        Ok(())
    }
}
