use crate::encoder::{
    errors::SpannedEncodingResult, high::procedures::HighProcedureEncoderInterface,
    mir::specifications::SpecificationsInterface,
};
use log::debug;
use prusti_common::config;
use prusti_rustc_interface::{hir::def_id::DefId, middle::ty};
use vir_crate::{
    common::{check_mode::CheckMode, identifier::WithIdentifier},
    low::{self as vir_low},
};

#[derive(Default)]
pub(crate) struct MidCoreProofEncoderState {
    encoded_programs: Vec<vir_low::Program>,
}

pub(crate) trait MidCoreProofEncoderInterface<'tcx> {
    fn encode_lifetimes_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<()>;
    fn encode_core_proof_for_type(
        &mut self,
        ty: ty::Ty<'tcx>,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<()>;
    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program>;
}

impl<'v, 'tcx: 'v> MidCoreProofEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    #[tracing::instrument(level = "debug", skip(self))]
    fn encode_lifetimes_core_proof(
        &mut self,
        proc_def_id: DefId,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<()> {
        if self.is_trusted(proc_def_id, None) {
            debug!(
                "Trusted procedure will not be encoded or verified: {:?}",
                proc_def_id
            );
            return Ok(());
        }
        let procedure = self.encode_procedure_core_proof(proc_def_id, check_mode)?;
        let super::lowerer::LoweringResult {
            procedures,
            domains,
            functions,
            predicates,
            methods,
        } = super::lowerer::lower_procedure(self, proc_def_id, procedure)?;
        let mut program = vir_low::Program {
            name: self.env().name.get_absolute_item_name(proc_def_id),
            check_mode,
            procedures,
            domains,
            predicates,
            functions,
            methods,
        };
        if config::inline_caller_for() {
            super::transformations::inline_functions::inline_caller_for(&mut program);
        }
        self.mid_core_proof_encoder_state
            .encoded_programs
            .push(program);
        Ok(())
    }

    fn encode_core_proof_for_type(
        &mut self,
        ty: ty::Ty<'tcx>,
        check_mode: CheckMode,
    ) -> SpannedEncodingResult<()> {
        let (check_copy, def_id) = if ty.is_trivially_pure_clone_copy() {
            (true, None)
        } else if let ty::TyKind::Adt(adt_def, ..) = ty.kind() {
            let param_env = self.env().tcx().param_env(adt_def.did());
            // FIXME: Figure out how to reuse Environment::type_is_copy
            // function.
            (
                ty.is_copy_modulo_regions(
                    *self.env().tcx().at(prusti_rustc_interface::span::DUMMY_SP),
                    param_env,
                ),
                Some(adt_def.did()),
            )
        } else {
            // We conservatively mark types as copy here because if they are
            // not, we will simply get a verification error.
            (true, None)
        };
        let ty = self.encode_type_core_proof(ty, check_mode)?;
        let name = ty.get_identifier();
        let super::lowerer::LoweringResult {
            procedures,
            domains,
            functions,
            predicates,
            methods,
        } = super::lowerer::lower_type(self, def_id, ty, check_copy)?;
        assert!(procedures.is_empty());
        let mut program = vir_low::Program {
            name,
            check_mode,
            procedures: vec![],
            domains,
            predicates,
            functions,
            methods,
        };
        if config::inline_caller_for() {
            super::transformations::inline_functions::inline_caller_for(&mut program);
        }
        self.mid_core_proof_encoder_state
            .encoded_programs
            .push(program);
        Ok(())
    }

    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program> {
        std::mem::take(&mut self.mid_core_proof_encoder_state.encoded_programs)
    }
}
