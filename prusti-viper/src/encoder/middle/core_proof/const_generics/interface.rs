use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::Lowerer,
        snapshots::{IntoProcedureSnapshot, IntoPureSnapshot},
    },
};

use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid, operations::const_generics::WithConstArguments},
};

pub(in super::super) trait ConstGenericsInterface {
    fn create_const_parameters(
        &mut self,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>>;
    fn create_const_arguments<G>(
        &mut self,
        context: CallContext,
        type_decl: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>
    where
        G: WithConstArguments;
}

impl<'p, 'v: 'p, 'tcx: 'v> ConstGenericsInterface for Lowerer<'p, 'v, 'tcx> {
    fn create_const_parameters(
        &mut self,
        type_decl: &vir_mid::TypeDecl,
    ) -> SpannedEncodingResult<Vec<vir_low::VariableDecl>> {
        let mut parameters = Vec::new();
        for parameter in type_decl.get_const_parameters() {
            parameters.push(parameter.to_pure_snapshot(self)?);
        }
        Ok(parameters)
    }

    fn create_const_arguments<G>(
        &mut self,
        context: CallContext,
        generics: &G,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>>
    where
        G: WithConstArguments,
    {
        let mut arguments = Vec::new();
        for argument in generics.get_const_arguments() {
            let argument = match context {
                CallContext::BuiltinMethod => argument.to_pure_snapshot(self)?,
                CallContext::Procedure => argument.to_procedure_snapshot(self)?,
            };
            arguments.push(argument);
        }
        Ok(arguments)
    }
}
