use crate::encoder::{
    borrows::ProcedureContractMirDef,
    encoder::SubstMap,
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        places::PlacesEncoderInterface,
        pure::{
            interpreter::ExpressionBackwardInterpreter,
            specifications::SpecificationEncoderInterface,
        },
        types::MirTypeEncoderInterface,
    },
    mir_encoder::{MirEncoder, PlaceEncoder},
    mir_interpreter::run_backward_interpretation,
    Encoder,
};
use log::{debug, trace};
use prusti_common::vir_high_local;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use rustc_span::Span;
use vir_crate::{
    common::expression::ExpressionIterator,
    high::{self as vir_high},
};

use super::encoder::FunctionCallInfoHigh;

pub(super) fn encode_function_decl<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
) -> SpannedEncodingResult<vir_high::FunctionDecl> {
    let interpreter = ExpressionBackwardInterpreter::new(
        encoder,
        mir,
        proc_def_id,
        false,
        parent_def_id,
        tymap.clone(),
    );
    let encoder = PureEncoder {
        encoder,
        proc_def_id,
        mir,
        parent_def_id,
        tymap,
        interpreter,
    };
    encoder.encode_function_decl()
    // FIXME: Traverse the encoded function and check that all used types are
    // Copy. Doing this before encoding causes too many false positives.
}

pub(super) fn encode_pure_expression<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
) -> SpannedEncodingResult<vir_high::Expression> {
    let interpreter = ExpressionBackwardInterpreter::new(
        encoder,
        mir,
        proc_def_id,
        false,
        parent_def_id,
        tymap.clone(),
    );
    let encoder = PureEncoder {
        encoder,
        proc_def_id,
        mir,
        parent_def_id,
        tymap,
        interpreter,
    };
    encoder.encode_pure_expression()
    // FIXME: Traverse the encoded function and check that all used types are
    // Copy. Doing this before encoding causes too many false positives.
}

pub(super) fn encode_function_call_info<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
) -> SpannedEncodingResult<FunctionCallInfoHigh> {
    // FIXME: Refactor code to avoid creating the interpreter because it is unnecessary.
    let interpreter = ExpressionBackwardInterpreter::new(
        encoder,
        mir,
        proc_def_id,
        false,
        parent_def_id,
        tymap.clone(),
    );
    let encoder = PureEncoder {
        encoder,
        proc_def_id,
        mir,
        parent_def_id,
        tymap,
        interpreter,
    };
    Ok(FunctionCallInfoHigh {
        name: encoder.encode_function_name(),
        _parameters: encoder.encode_parameters()?,
        return_type: encoder.encode_return_type()?,
    })
}

/// Encoder of pure things such as pure functions and specification assertions.
pub(super) struct PureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    interpreter: ExpressionBackwardInterpreter<'p, 'v, 'tcx>,
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> PureEncoder<'p, 'v, 'tcx> {
    fn encode_pure_expression(&self) -> SpannedEncodingResult<vir_high::Expression> {
        let state = run_backward_interpretation(self.mir, &self.interpreter)?.ok_or_else(|| {
            SpannedEncodingError::incorrect(
                format!("procedure {:?} contains a loop", self.proc_def_id),
                self.encoder.env().get_def_span(self.proc_def_id),
            )
        })?;
        let body = state.into_expr().ok_or_else(|| {
            SpannedEncodingError::internal(
                format!("failed to encode function's body: {:?}", self.proc_def_id),
                self.encoder.env().get_def_span(self.proc_def_id),
            )
        })?;
        debug!(
            "Pure function {:?} has been encoded with expr: {}",
            self.proc_def_id, body
        );
        // FIXME: Apply type substitutions.
        Ok(body)
    }

    fn encode_function_decl(&self) -> SpannedEncodingResult<vir_high::FunctionDecl> {
        trace!("[enter] encode_function({:?})", self.proc_def_id);
        let body = Some(self.encode_pure_expression()?);
        let function = self.encode_function_decl_given_body(body);
        trace!("[exit] encode_function({:?})", self.proc_def_id);
        function
    }

    fn encode_function_name(&self) -> String {
        self.encoder.encode_item_name(self.proc_def_id)
    }

    fn encode_function_decl_given_body(
        &self,
        body: Option<vir_high::Expression>,
    ) -> SpannedEncodingResult<vir_high::FunctionDecl> {
        trace!(
            "[enter] encode_function_decl_given_body({:?})",
            self.proc_def_id
        );
        let name = self.encode_function_name();
        let parameters = self.encode_parameters()?;
        let return_type = self.encode_return_type()?;

        let contract = self
            .encoder
            .get_mir_procedure_contract_for_def(self.proc_def_id)
            .with_span(self.mir.span)?;
        let func_precondition = self.encode_precondition_expr(&parameters, &contract)?;
        let func_postcondition = self.encode_postcondition_expr(&parameters, &contract)?;

        let function = vir_high::FunctionDecl {
            name,
            parameters,
            return_type,
            pres: vec![func_precondition],
            posts: vec![func_postcondition],
            body,
        };
        trace!(
            "[exit] encode_function_decl_given_body({:?})",
            self.proc_def_id
        );
        Ok(function)
    }

    fn encode_parameters(&self) -> SpannedEncodingResult<Vec<vir_high::VariableDecl>> {
        let mut parameters = Vec::new();
        for local in self.mir.args_iter() {
            let ty = self.encoder.get_local_type(self.mir, local)?;
            let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
            if !self
                .encoder
                .env()
                .type_is_allowed_in_pure_functions(ty, param_env)
            {
                return Err(SpannedEncodingError::incorrect(
                    "all types used in pure functions must be Copy",
                    self.encoder.get_local_span(self.mir, local)?,
                ));
            }
            let variable_decl = self.encode_mir_local(local)?;
            parameters.push(variable_decl);
        }

        Ok(parameters)
    }

    fn convert_parameters_into_expressions(
        &self,
        parameters: &[vir_high::VariableDecl],
    ) -> Vec<vir_high::Expression> {
        parameters
            .iter()
            .map(|parameter| vir_high::Expression::local_no_pos(parameter.clone()))
            .collect()
    }

    fn encode_return_type(&self) -> SpannedEncodingResult<vir_high::Type> {
        let ty = self.mir.return_ty();
        let span = self.get_local_span(mir::RETURN_PLACE);
        let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
        if !self
            .encoder
            .env()
            .type_is_allowed_in_pure_functions(ty, param_env)
        {
            return Err(SpannedEncodingError::incorrect(
                "return type of pure function does not implement Copy",
                span,
            ));
        }
        self.encoder.encode_type_high(ty)
    }

    fn encode_mir_local(&self, local: mir::Local) -> SpannedEncodingResult<vir_high::VariableDecl> {
        let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
        if !self.encoder.is_local_copy(self.mir, local, param_env)? {
            return Err(SpannedEncodingError::incorrect(
                "pure function parameters must be Copy",
                self.encoder.get_local_span(self.mir, local)?,
            ));
        }
        self.encoder.encode_local_high(self.mir, local)
    }

    fn encode_precondition_expr(
        &self,
        parameters: &[vir_high::VariableDecl],
        contract: &ProcedureContractMirDef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let parameter_expressions = self.convert_parameters_into_expressions(parameters);
        let mut conjuncts = Vec::new();
        for item in contract.functional_precondition() {
            conjuncts.push(self.encoder.encode_assertion_high(
                item,
                self.mir,
                None,
                &parameter_expressions,
                None,
                None,
                ErrorCtxt::GenericExpression,
                self.parent_def_id,
                self.tymap,
            )?);
        }
        Ok(conjuncts.into_iter().conjoin())
    }

    fn encode_postcondition_expr(
        &self,
        parameters: &[vir_high::VariableDecl],
        contract: &ProcedureContractMirDef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let parameter_expressions = self.convert_parameters_into_expressions(parameters);
        let mut conjuncts = Vec::new();
        let encoded_return = self.encode_mir_local(contract.returned_value)?;
        for item in contract.functional_postcondition() {
            conjuncts.push(self.encoder.encode_assertion_high(
                item,
                self.mir,
                None,
                &parameter_expressions,
                Some(&vir_high::Expression::local_no_pos(encoded_return.clone())),
                None,
                ErrorCtxt::GenericExpression,
                self.parent_def_id,
                self.tymap,
            )?);
        }
        let post = conjuncts.into_iter().conjoin();

        // TODO: use a better span
        let postcondition_pos = self.encoder.error_manager().register(
            self.mir.span,
            ErrorCtxt::GenericExpression,
            self.parent_def_id,
        );

        // Fix return variable
        let pure_fn_return_variable = vir_high_local! { __result: {self.encode_return_type()?} };

        let post = post
            .replace_place(&encoded_return.into(), &pure_fn_return_variable.into())
            .set_default_pos(postcondition_pos.into());

        Ok(post)
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        self.mir_encoder().get_local_span(local)
    }

    fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'tcx> {
        self.interpreter.mir_encoder()
    }
}
