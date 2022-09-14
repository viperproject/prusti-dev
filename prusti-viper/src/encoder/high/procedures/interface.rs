use crate::encoder::{
    errors::SpannedEncodingResult,
    high::to_middle::HighToMiddle,
    mir::{procedures::MirProcedureEncoderInterface, types::MirTypeEncoderInterface},
};
use prusti_rustc_interface::{hir::def_id::DefId, middle::ty};
use std::collections::BTreeMap;
use vir_crate::{
    common::check_mode::CheckMode,
    high as vir_high, middle as vir_mid,
    typed::{
        self as vir_typed,
        operations::{HighToTypedExpression, HighToTypedStatement},
    },
};

trait Private {
    fn procedure_high_to_typed(
        &mut self,
        procedure_high: vir_high::ProcedureDecl,
    ) -> SpannedEncodingResult<vir_typed::ProcedureDecl>;
    fn lower_block(
        &mut self,
        block: vir_high::BasicBlock,
    ) -> SpannedEncodingResult<vir_typed::BasicBlock>;
    fn lower_successor(
        &mut self,
        successor: vir_high::Successor,
    ) -> SpannedEncodingResult<vir_typed::Successor>;
}

impl<'v, 'tcx: 'v> Private for super::super::super::Encoder<'v, 'tcx> {
    fn lower_block(
        &mut self,
        block: vir_high::BasicBlock,
    ) -> SpannedEncodingResult<vir_typed::BasicBlock> {
        let mut statements = Vec::new();
        for statement in block.statements {
            statements.push(statement.high_to_typed_statement(self)?);
        }
        Ok(vir_typed::BasicBlock {
            statements,
            successor: self.lower_successor(block.successor)?,
        })
    }

    fn lower_successor(
        &mut self,
        successor: vir_high::Successor,
    ) -> SpannedEncodingResult<vir_typed::Successor> {
        let result = match successor {
            vir_high::Successor::Exit => vir_typed::Successor::Exit,
            vir_high::Successor::Goto(target) => {
                vir_typed::Successor::Goto(target.high_to_typed_statement(self)?)
            }
            vir_high::Successor::GotoSwitch(targets) => {
                let mut new_targets = Vec::new();
                for (test, target) in targets {
                    let new_test: vir_typed::Expression =
                        test.clone().high_to_typed_expression(self)?;
                    new_targets.push((new_test, target.high_to_typed_statement(self)?));
                }
                vir_typed::Successor::GotoSwitch(new_targets)
            }
            vir_high::Successor::NonDetChoice(first, second) => vir_typed::Successor::NonDetChoice(
                first.high_to_typed_statement(self)?,
                second.high_to_typed_statement(self)?,
            ),
        };
        Ok(result)
    }

    #[tracing::instrument(level = "debug", skip(self, procedure_high), fields(procedure = %procedure_high))]
    fn procedure_high_to_typed(
        &mut self,
        procedure_high: vir_high::ProcedureDecl,
    ) -> SpannedEncodingResult<vir_typed::ProcedureDecl> {
        let mut basic_blocks = BTreeMap::new();
        for (label, block) in procedure_high.basic_blocks {
            basic_blocks.insert(
                label.high_to_typed_statement(self)?,
                self.lower_block(block)?,
            );
        }
        let non_aliased_places = procedure_high
            .non_aliased_places
            .into_iter()
            .map(|place| place.high_to_typed_expression(self))
            .collect::<Result<_, _>>()?;
        let procedure_typed = vir_typed::ProcedureDecl {
            name: procedure_high.name,
            check_mode: procedure_high.check_mode,
            position: procedure_high.position,
            non_aliased_places,
            entry: procedure_high.entry.high_to_typed_statement(self)?,
            exit: procedure_high.exit.high_to_typed_statement(self)?,
            basic_blocks,
        };
        Ok(procedure_typed)
    }
}

pub(crate) trait HighProcedureEncoderInterface<'tcx> {
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<Vec<vir_mid::ProcedureDecl>>;
    fn encode_type_core_proof(
        &mut self,
        ty: ty::Ty<'tcx>,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_mid::Type>;
}

impl<'v, 'tcx: 'v> HighProcedureEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip(self))]
    fn encode_procedure_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<Vec<vir_mid::ProcedureDecl>> {
        let mut procedures = Vec::new();
        for procedure_high in self.encode_procedure_core_proof_high(proc_def_id, check_mode)? {
            let procedure_typed = self.procedure_high_to_typed(procedure_high)?;
            let procedure =
                super::inference::infer_shape_operations(self, proc_def_id, procedure_typed)?;
            procedures.push(procedure);
        }
        Ok(procedures)
    }

    fn encode_type_core_proof(
        &mut self,
        ty: ty::Ty<'tcx>,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<vir_mid::Type> {
        assert_eq!(check_mode, CheckMode::MemorySafety);
        let ty_high = self.encode_type_high(ty)?;
        ty_high.high_to_middle(self)
    }
}
