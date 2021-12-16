use super::{definition_collector, lower::IntoLow};
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::{
        expressions::HighExpressionEncoderInterface, procedures::HighProcedureEncoderInterface,
    },
    mir::procedures::MirProcedureEncoderInterface,
};
use rustc_hir::def_id::DefId;
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low, operations::ToLow},
    middle as vir_mid,
};

#[derive(Default)]
pub(crate) struct MidCoreProofEncoderState {
    encoded_programs: Vec<vir_low::Program>,
}

pub(crate) trait MidCoreProofEncoderInterface<'tcx> {
    fn encode_lifetimes_core_proof(&mut self, proc_def_id: DefId) -> SpannedEncodingResult<()>;
    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program>;
    fn lower_expression_into_low(&self, expression: vir_mid::Expression) -> vir_low::Expression;
    fn lower_type_into_low(&mut self, ty: vir_mid::Type) -> vir_low::ast::ty::Type;
}

impl<'v, 'tcx: 'v> MidCoreProofEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_lifetimes_core_proof(&mut self, proc_def_id: DefId) -> SpannedEncodingResult<()> {
        let procedure = self.encode_procedure_core_proof(proc_def_id)?;
        eprintln!("procedure:\n{}", procedure);
        let predicates = definition_collector::collect_predicates(&procedure);
        let functions = definition_collector::collect_functions(&procedure);
        let lowered_procedure = procedure.into_low(self);
        eprintln!("lowered_procedure:\n{}", lowered_procedure);
        let mut lowered_predicates = Vec::new();
        for predicate in predicates {
            // FIXME: Properly collect predicate definitions.

            // FIXME: There should be fold-unfold step that unifies
            // MemoryBlockHeap and MemoryBlockStack into MemoryBlock.
            let parameters = predicate
                .parameter_types()
                .into_iter()
                .enumerate()
                .map(|(index, ty)| {
                    vir_low::ast::variable::VariableDecl::new(
                        format!("_{}", index),
                        self.lower_type_into_low(ty),
                    )
                })
                .collect();
            lowered_predicates.push(vir_low::ast::predicate::PredicateDecl {
                name: predicate.get_identifier(),
                parameters,
                body: None,
            });
        }
        let mut lowered_functions = Vec::new();
        for function in functions {
            lowered_functions.push(function.into_low(self));
        }
        let program = vir_low::Program {
            name: self.env().get_absolute_item_name(proc_def_id),
            procedures: vec![lowered_procedure],
            predicates: lowered_predicates,
            functions: lowered_functions,
            // domains: Vec::new(),
            // fields: Vec::new(),
            // builtin_methods: Vec::new(),
            // methods: vec![lowered_procedure],
            // functions: Vec::new(),
            // viper_predicates: Vec::new(),
        };
        self.mid_core_proof_encoder_state
            .encoded_programs
            .push(program);
        Ok(())
    }
    fn take_core_proof_programs(&mut self) -> Vec<vir_low::Program> {
        std::mem::take(&mut self.mid_core_proof_encoder_state.encoded_programs)
    }
    fn lower_expression_into_low(&self, expression: vir_mid::Expression) -> vir_low::Expression {
        expression.to_low(self)
    }
    fn lower_type_into_low(&mut self, ty: vir_mid::Type) -> vir_low::ast::ty::Type {
        ty.to_low(self)
    }
}
