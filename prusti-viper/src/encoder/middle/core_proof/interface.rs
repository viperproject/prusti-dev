use crate::encoder::{
    errors::SpannedEncodingResult, high::procedures::HighProcedureEncoderInterface,
    mir::specifications::SpecificationsInterface,
};
use log::{debug, info};
use prusti_common::config;
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::{hir::def_id::DefId, middle::ty};
use vir_crate::{
    common::{check_mode::CheckMode, identifier::WithIdentifier},
    low::{self as vir_low},
};

#[derive(Default)]
pub(crate) struct MidCoreProofEncoderState {
    encoded_programs: Vec<(Option<ProcedureDefId>, vir_low::Program)>,
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
    fn take_core_proof_programs(&mut self) -> Vec<(Option<ProcedureDefId>, vir_low::Program)>;
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
        for procedure in self.encode_procedure_core_proof(proc_def_id, check_mode)? {
            info!(
                "Lowering procedure: {} ({proc_def_id:?} {check_mode:?})",
                procedure.name
            );
            let name = procedure.name.clone();
            let super::lowerer::LoweringResult {
                procedures,
                domains,
                functions,
                predicates,
                methods,
                domains_info: _,
                predicates_info,
                snapshot_domains_info,
                extensionality_gas_constant,
            } = super::lowerer::lower_procedure(self, proc_def_id, procedure)?;
            let mut program = vir_low::Program {
                name,
                // name: self.env().name.get_absolute_item_name(proc_def_id),
                check_mode,
                procedures,
                domains,
                predicates,
                functions,
                methods,
            };
            let source_filename = self.env().name.source_file_name();
            if config::trace_with_symbolic_execution() || config::custom_heap_encoding() {
                program = super::transformations::desugar_method_calls::desugar_method_calls(
                    &source_filename,
                    program,
                );
                program = super::transformations::desugar_fold_unfold::desugar_fold_unfold(
                    &source_filename,
                    program,
                    &predicates_info.owned_predicates_info,
                );
                program = super::transformations::desugar_implications::desugar_implications(
                    &source_filename,
                    program,
                );
                program = super::transformations::desugar_conditionals::desugar_conditionals(
                    &source_filename,
                    program,
                );
            }
            if config::inline_caller_for()
                || config::trace_with_symbolic_execution()
                || config::custom_heap_encoding()
            {
                super::transformations::inline_functions::inline_caller_for(
                    &source_filename,
                    &mut program,
                );
            }
            if config::trace_with_symbolic_execution() {
                if config::trace_with_symbolic_execution_new() {
                    program =
                        super::transformations::make_all_jumps_nondeterministic::make_all_jumps_nondeterministic(
                            &source_filename,
                            program
                        );
                    program =
                        super::transformations::merge_consequent_blocks::merge_consequent_blocks(
                            &source_filename,
                            program,
                        );
                    program =
                        super::transformations::symbolic_execution_new::purify_with_symbolic_execution(
                            self,
                            &source_filename,
                            program,
                            predicates_info.non_aliased_memory_block_addresses.clone(),
                            &snapshot_domains_info,
                            predicates_info.owned_predicates_info.clone(),
                            &extensionality_gas_constant,
                        )?;
                } else {
                    program =
                        super::transformations::symbolic_execution::purify_with_symbolic_execution(
                            self,
                            &source_filename,
                            program,
                            predicates_info.non_aliased_memory_block_addresses.clone(),
                            &snapshot_domains_info,
                            predicates_info.owned_predicates_info.clone(),
                            &extensionality_gas_constant,
                            2,
                        )?;
                }
                // program =
                //     super::transformations::symbolic_execution::purify_with_symbolic_execution(
                //         &source_filename,
                //         program,
                //         predicates_info.non_aliased_memory_block_addresses,
                //         &snapshot_domains_info,
                //         predicates_info.owned_predicates_info.clone(),
                //         2,
                //     )?;
            }
            if config::custom_heap_encoding() {
                super::transformations::custom_heap_encoding::custom_heap_encoding(
                    self,
                    &mut program,
                    predicates_info.owned_predicates_info,
                )?;
            }
            if config::expand_quantifiers() {
                program = super::transformations::expand_quantifiers::expand_quantifiers(
                    &source_filename,
                    program,
                );
            }
            // We have to execute this pass because some of the transformations
            // generate nested old expressions, which cause problems when
            // triggering.
            program = super::transformations::clean_old::clean_old(&source_filename, program);
            // We have to execute this pass because some of the transformations
            // generate unused variables whose types are not defined.
            program =
                super::transformations::clean_variables::clean_variables(&source_filename, program);
            self.mid_core_proof_encoder_state
                .encoded_programs
                .push((Some(proc_def_id), program));
        }
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
            domains_info: _,
            snapshot_domains_info: _,
            predicates_info: _,
            extensionality_gas_constant: _,
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
            let source_filename = self.env().name.source_file_name();
            super::transformations::inline_functions::inline_caller_for(
                &source_filename,
                &mut program,
            );
        }
        self.mid_core_proof_encoder_state
            .encoded_programs
            .push((None, program));
        Ok(())
    }

    fn take_core_proof_programs(&mut self) -> Vec<(Option<ProcedureDefId>, vir_low::Program)> {
        std::mem::take(&mut self.mid_core_proof_encoder_state.encoded_programs)
    }
}
