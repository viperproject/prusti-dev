use super::{encoder::FunctionCallInfoHigh, PureEncodingContext};
use crate::encoder::{
    borrows::ProcedureContractMirDef,
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    mir::{
        generics::MirGenericsEncoderInterface,
        pure::{
            interpreter::ExpressionBackwardInterpreter,
            specifications::SpecificationEncoderInterface,
        },
        specifications::SpecificationsInterface,
        types::MirTypeEncoderInterface,
    },
    mir_interpreter::run_backward_interpretation,
    Encoder,
};

use log::{debug, trace};
use prusti_common::vir_high_local;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty, ty::subst::SubstsRef};
use rustc_span::Span;
use vir_crate::{
    common::{expression::ExpressionIterator, position::Positioned},
    high::{self as vir_high},
};

pub(super) fn encode_function_decl<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir_high::FunctionDecl> {
    let pure_encoder = PureEncoder::new(
        encoder,
        proc_def_id,
        PureEncodingContext::Code,
        parent_def_id,
        substs,
    );
    let function_decl = pure_encoder.encode_function_decl()?;
    if function_decl.body.is_some() {
        // Check that function does not call itself in its contract.
        let span = encoder.env().get_def_span(proc_def_id);
        struct CallFinder<'a> {
            function_name: &'a str,
            span: Span,
        }
        impl<'a> vir_high::visitors::ExpressionFallibleWalker for CallFinder<'a> {
            type Error = SpannedEncodingError;
            fn fallible_walk_func_app(
                &mut self,
                func_app: &vir_high::FuncApp,
            ) -> Result<(), Self::Error> {
                if func_app.function_name == self.function_name {
                    return Err(SpannedEncodingError::incorrect(
                        "only trusted functions can call themselves in their contracts".to_string(),
                        self.span,
                    ));
                }
                vir_high::visitors::default_fallible_walk_func_app(self, func_app)
            }
        }
        let mut finder = CallFinder {
            span,
            function_name: &function_decl.name,
        };
        for expr in function_decl.pres.iter().chain(&function_decl.posts) {
            vir_high::visitors::ExpressionFallibleWalker::fallible_walk_expression(
                &mut finder,
                expr,
            )?;
        }
    }
    // FIXME: Traverse the encoded function and check that all used types are
    // Copy. Doing this before encoding causes too many false positives.
    Ok(function_decl)
}

pub(super) fn encode_pure_expression<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    pure_encoding_context: PureEncodingContext,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir_high::Expression> {
    let mir = encoder.env().local_mir(proc_def_id.expect_local(), substs);
    let interpreter = ExpressionBackwardInterpreter::new(
        encoder,
        &mir,
        proc_def_id,
        pure_encoding_context,
        parent_def_id,
        substs,
    );
    let state = run_backward_interpretation(&mir, &interpreter)?.ok_or_else(|| {
        SpannedEncodingError::incorrect(
            format!("procedure {:?} contains a loop", proc_def_id),
            encoder.env().get_def_span(proc_def_id),
        )
    })?;
    let body = state.into_expr().ok_or_else(|| {
        SpannedEncodingError::internal(
            format!("failed to encode function's body: {:?}", proc_def_id),
            encoder.env().get_def_span(proc_def_id),
        )
    })?;
    debug!(
        "Pure function {:?} has been encoded with expr: {}",
        proc_def_id, body
    );
    // FIXME: Traverse the encoded function and check that all used types are
    // Copy. Doing this before encoding causes too many false positives.
    Ok(body)
}

pub(super) fn encode_function_call_info<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<FunctionCallInfoHigh> {
    let encoder = PureEncoder::new(
        encoder,
        proc_def_id,
        PureEncodingContext::Code,
        parent_def_id,
        substs,
    );
    Ok(FunctionCallInfoHigh {
        name: encoder.encode_function_name(),
        type_arguments: encoder.encode_type_arguments()?,
        return_type: encoder.encode_return_type()?,
    })
}

/// Encoder of pure things such as pure functions and specification assertions.
pub(super) struct PureEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// The function to be encoded.
    proc_def_id: DefId,
    /// Where is this being encoded?
    pure_encoding_context: PureEncodingContext,
    parent_def_id: DefId,
    /// Type substitutions applied to the MIR (if any) and the signature.
    substs: SubstsRef<'tcx>,
    /// Span of the function declaration.
    span: Span,
    /// Signature of the function to be encoded.
    sig: ty::PolyFnSig<'tcx>,
    /// Spans of MIR locals, when encoding a local pure function.
    local_spans: Option<Vec<Span>>,
}

impl<'p, 'v: 'p, 'tcx: 'v> PureEncoder<'p, 'v, 'tcx> {
    fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        pure_encoding_context: PureEncodingContext,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Self {
        trace!("PureEncoder constructor: {:?}", proc_def_id);

        // should hold for extern specs as well (otherwise there would have
        // been an error reported earlier)
        assert_eq!(
            substs.len(),
            encoder.env().identity_substs(proc_def_id).len()
        );

        let span = encoder.get_spec_span(proc_def_id);

        // TODO: move this to a signatures module
        use crate::rustc_middle::ty::subst::Subst;
        let sig = encoder
            .env()
            .tcx()
            .fn_sig(proc_def_id)
            .subst(encoder.env().tcx(), substs);

        Self {
            encoder,
            proc_def_id,
            pure_encoding_context,
            parent_def_id,
            substs,
            span,
            sig,
            local_spans: None,
        }
    }

    fn encode_function_decl(&self) -> SpannedEncodingResult<vir_high::FunctionDecl> {
        trace!("[enter] encode_function_decl({:?})", self.proc_def_id);
        let mir = self
            .encoder
            .env()
            .local_mir(self.proc_def_id.expect_local(), self.substs);
        let interpreter = ExpressionBackwardInterpreter::new(
            self.encoder,
            &mir,
            self.proc_def_id,
            self.pure_encoding_context,
            self.parent_def_id,
            self.substs,
        );

        let state = run_backward_interpretation(&mir, &interpreter)?.ok_or_else(|| {
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
        let function = self.encode_function_decl_given_body(Some(body));
        trace!("[exit] encode_function_decl({:?})", self.proc_def_id);
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
            .get_mir_procedure_contract_for_def(self.proc_def_id, self.substs)
            .with_span(self.span)?;
        let func_precondition = self.encode_precondition_expr(&parameters, &contract)?;
        let func_postcondition = self.encode_postcondition_expr(&parameters, &contract)?;
        let type_arguments = self.encode_type_arguments()?;

        let function = vir_high::FunctionDecl {
            name,
            type_arguments,
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

    fn encode_type_arguments(&self) -> SpannedEncodingResult<Vec<vir_high::Type>> {
        self.encoder
            .encode_generic_arguments_high(self.proc_def_id, self.substs)
            .with_span(self.span)
    }

    fn encode_parameters(&self) -> SpannedEncodingResult<Vec<vir_high::VariableDecl>> {
        let mut parameters = Vec::new();
        for local in self.args_iter() {
            let ty = self.get_local_ty(local);
            let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
            if !self
                .encoder
                .env()
                .type_is_allowed_in_pure_functions(ty, param_env)
            {
                return Err(SpannedEncodingError::incorrect(
                    "all types used in pure functions must be Copy",
                    self.get_local_span(local),
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
        let ty = self.sig.output();

        let span = self.get_return_span();
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

        self.encoder.encode_type_high(ty.skip_binder())
    }

    fn encode_precondition_expr(
        &self,
        parameters: &[vir_high::VariableDecl],
        contract: &ProcedureContractMirDef<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let parameter_expressions = self.convert_parameters_into_expressions(parameters);
        let mut conjuncts = Vec::new();
        for (assertion, assertion_substs) in
            contract.functional_precondition(self.encoder.env(), self.substs)
        {
            let encoded_assertion = self.encoder.encode_assertion_high(
                &assertion,
                None,
                &parameter_expressions,
                None,
                self.parent_def_id,
                assertion_substs,
            )?;
            self.encoder.error_manager().set_error(
                encoded_assertion.position().into(),
                ErrorCtxt::PureFunctionDefinition,
            );
            conjuncts.push(encoded_assertion);
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
        for (assertion, assertion_substs) in
            contract.functional_postcondition(self.encoder.env(), self.substs)
        {
            let encoded_assertion = self.encoder.encode_assertion_high(
                &assertion,
                None,
                &parameter_expressions,
                Some(&vir_high::Expression::local_no_pos(encoded_return.clone())),
                self.parent_def_id,
                assertion_substs,
            )?;
            self.encoder.error_manager().set_error(
                encoded_assertion.position().into(),
                ErrorCtxt::PureFunctionDefinition,
            );
            conjuncts.push(encoded_assertion);
        }
        let post = conjuncts.into_iter().conjoin();

        // TODO: use a better span
        let postcondition_pos = self.encoder.error_manager().register_error(
            self.span,
            ErrorCtxt::PureFunctionDefinition,
            self.parent_def_id,
        );

        // Fix return variable
        let pure_fn_return_variable = vir_high_local! { __result: {self.encode_return_type()?} };

        let post = post
            .replace_place(&encoded_return.into(), &pure_fn_return_variable.into())
            .set_default_position(postcondition_pos.into());

        Ok(post)
    }

    fn args_iter(&self) -> impl Iterator<Item = mir::Local> {
        (0..self.sig.inputs().skip_binder().len()).map(|idx| mir::Local::from_usize(1 + idx))
    }

    /// Encodes a VIR local with the original MIR type.
    fn encode_mir_local(&self, local: mir::Local) -> SpannedEncodingResult<vir_high::VariableDecl> {
        let ty = self.get_local_ty(local);
        let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
        if !self
            .encoder
            .env()
            .type_is_allowed_in_pure_functions(ty, param_env)
        {
            return Err(SpannedEncodingError::incorrect(
                "pure function parameters must be Copy",
                self.get_local_span(local),
            ));
        }
        let var_name = format!("{:?}", local);
        let var_type = self.encoder.encode_type_high(ty.skip_binder())?;
        Ok(vir_high::VariableDecl {
            name: var_name,
            ty: var_type,
        })
    }

    fn get_local_ty(&self, local: mir::Local) -> ty::Binder<'tcx, ty::Ty<'tcx>> {
        if local.as_usize() == 0 {
            self.sig.output()
        } else {
            self.sig.input(local.as_usize() - 1)
        }
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        self.local_spans
            .as_ref()
            .map(|spans| spans[local.index()])
            .unwrap_or(self.span)
    }

    fn get_return_span(&self) -> Span {
        self.get_local_span(mir::RETURN_PLACE)
    }
}
