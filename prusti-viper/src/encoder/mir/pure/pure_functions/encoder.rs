// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::interpreter::PureFunctionBackwardInterpreter;
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    high::{generics::HighGenericsEncoderInterface, types::HighTypeEncoderInterface},
    mir::{
        contracts::{ContractsEncoderInterface, ProcedureContract},
        pure::{PureEncodingContext, SpecificationEncoderInterface},
        specifications::SpecificationsInterface,
    },
    mir_encoder::PlaceEncoder,
    mir_interpreter::run_backward_interpretation,
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use log::{debug, trace};
use prusti_common::{config, vir::optimizations::functions::Simplifier, vir_local};

use prusti_rustc_interface::{
    hir,
    hir::def_id::{DefId, LocalDefId},
    middle::{mir, ty, ty::subst::SubstsRef},
    span::Span,
};

use vir_crate::{
    common::identifier::WithIdentifier,
    high as vir_high,
    high::operations::identifier::compute_function_identifier,
    polymorphic::{self as vir, ExprIterator},
};

pub(super) struct PureFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
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

/// Used to encode expressions in assertions
pub(super) fn encode_body<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    pure_encoding_context: PureEncodingContext,
    parent_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> SpannedEncodingResult<vir::Expr> {
    let mir = encoder.env().local_mir(proc_def_id.expect_local(), substs);
    let interpreter = PureFunctionBackwardInterpreter::new(
        encoder,
        &mir,
        proc_def_id,
        pure_encoding_context,
        parent_def_id,
    );

    let function_name = encoder.env().get_absolute_item_name(proc_def_id);
    debug!("Encode body of pure function {}", function_name);

    let state = run_backward_interpretation(&mir, &interpreter)?
        .unwrap_or_else(|| panic!("Procedure {:?} contains a loop", proc_def_id));
    let body_expr = state.into_expr().unwrap();
    debug!(
        "Pure function body {} has been encoded with expr: {}",
        function_name, body_expr
    );

    Ok(body_expr)
}

impl<'p, 'v: 'p, 'tcx: 'v> PureFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        pure_encoding_context: PureEncodingContext,
        parent_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Self {
        trace!("PureFunctionEncoder constructor: {:?}", proc_def_id);

        // should hold for extern specs as well (otherwise there would have
        // been an error reported earlier)
        assert_eq!(
            substs.len(),
            encoder.env().identity_substs(proc_def_id).len()
        );

        let span = encoder.get_spec_span(proc_def_id);

        // TODO: move this to a signatures module
        use prusti_rustc_interface::middle::ty::subst::Subst;
        let sig = ty::EarlyBinder(encoder.env().tcx().fn_sig(proc_def_id))
            .subst(encoder.env().tcx(), substs);
        let sig = encoder
            .env()
            .resolve_assoc_types(sig, encoder.env().tcx().param_env(proc_def_id));

        PureFunctionEncoder {
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

    pub fn encode_function(&mut self) -> SpannedEncodingResult<vir::Function> {
        let mir = self
            .encoder
            .env()
            .local_mir(self.proc_def_id.expect_local(), self.substs);
        let interpreter = PureFunctionBackwardInterpreter::new(
            self.encoder,
            &mir,
            self.proc_def_id,
            self.pure_encoding_context,
            self.parent_def_id,
        );

        self.local_spans = Some(
            (0..=self.sig.skip_binder().inputs().len())
                .map(|idx| {
                    interpreter
                        .mir_encoder()
                        .get_local_span(mir::Local::from_usize(idx))
                })
                .collect(),
        );

        let function_name = self.encode_function_name();
        debug!("Encode pure function {}", function_name);
        let mut state = run_backward_interpretation(&mir, &interpreter)?
            .unwrap_or_else(|| panic!("Procedure {:?} contains a loop", self.proc_def_id));

        // Fix arguments
        if let Some(curr_expr) = state.expr_mut() {
            // Replace two times to avoid cloning `expr`, which could be big.
            let expr = std::mem::replace(curr_expr, true.into());
            let new_expr = self.fix_arguments(expr)?;
            let _ = std::mem::replace(curr_expr, new_expr);
        }

        let mut body_expr = state.into_expr().unwrap();
        debug!(
            "Pure function {} has been encoded with expr: {}",
            function_name, body_expr
        );

        // if the function returns a snapshot, we take a snapshot of the body
        if self.encode_function_return_type()?.is_snapshot() {
            let ty = self.sig.output();
            let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);

            if !self.encoder.env().type_is_copy(ty, param_env) {
                return Err(SpannedEncodingError::unsupported(
                    "return type of pure function does not implement Copy",
                    self.get_return_span(),
                ));
            }

            body_expr = vir::Expr::snap_app(body_expr);
        }
        self.encode_function_given_body(Some(body_expr))
    }

    pub fn encode_bodyless_function(&self) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        debug!("Encode trusted (bodyless) pure function {}", function_name);

        self.encode_function_given_body(None)
    }

    pub fn encode_predicate_function(
        &self,
        predicate_body: &LocalDefId,
    ) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        debug!("Encode predicate function {}", function_name);

        let contract = self
            .encoder
            .get_procedure_contract_for_def(self.proc_def_id, self.substs)
            .with_span(self.span)?;
        let encoded_args = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()).map(|l| l.into()))
            .collect::<Result<Vec<_>, _>>()?;

        let predicate_body_encoded = self.encoder.encode_assertion(
            predicate_body,
            None,
            &encoded_args,
            None,
            true,
            self.parent_def_id,
            self.substs,
        )?;
        self.encoder.error_manager().set_error(
            predicate_body_encoded.pos(),
            ErrorCtxt::PureFunctionDefinition,
        );

        self.encode_function_given_body(Some(predicate_body_encoded))
    }

    // Private

    fn encode_function_given_body(
        &self,
        body: Option<vir::Expr>,
    ) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        let is_bodyless = body.is_none();
        if is_bodyless {
            debug!("Encode pure function {} given body None", function_name);
        } else {
            debug!(
                "Encode pure function {} given body Some({})",
                function_name,
                body.as_ref().unwrap()
            );
        }

        let contract = self
            .encoder
            .get_procedure_contract_for_def(self.proc_def_id, self.substs)
            .with_span(self.span)?;

        let (type_precondition, func_precondition) = self.encode_precondition_expr(&contract)?;

        let mut precondition = vec![type_precondition, func_precondition];
        let mut postcondition = vec![self.encode_postcondition_expr(&contract)?];

        let formal_args = self.encode_formal_args()?;
        let return_type = self.encode_function_return_type()?;

        let res_value_range_pos = self.encoder.error_manager().register_error(
            self.span,
            ErrorCtxt::PureFunctionPostconditionValueRangeOfResult,
            self.parent_def_id,
        );
        let pure_fn_return_variable = vir_local! { __result: {return_type.clone()} };
        // Add value range of the arguments and return value to the pre/postconditions
        if config::check_overflows() {
            debug_assert!(self.encoder.env().type_is_copy(
                self.sig.output(),
                self.encoder.env().tcx().param_env(self.proc_def_id)
            ));
            let mut return_bounds: Vec<_> = self
                .encoder
                .encode_type_bounds(
                    &vir::Expr::local(pure_fn_return_variable),
                    self.sig.skip_binder().output(),
                )
                .into_iter()
                .map(|p| p.set_default_pos(res_value_range_pos))
                .collect();
            return_bounds.extend(postcondition);
            postcondition = return_bounds;

            for (formal_arg, local) in formal_args.iter().zip(self.args_iter()) {
                let typ = self.get_local_ty(local);
                debug_assert!(self
                    .encoder
                    .env()
                    .type_is_copy(typ, self.encoder.env().tcx().param_env(self.proc_def_id)));
                let mut bounds = self
                    .encoder
                    .encode_type_bounds(&vir::Expr::local(formal_arg.clone()), typ.skip_binder());
                bounds.extend(precondition);
                precondition = bounds;
            }
        } else if config::encode_unsigned_num_constraint() {
            if let ty::TyKind::Uint(_) = self.sig.skip_binder().output().kind() {
                let expr = vir::Expr::le_cmp(0u32.into(), pure_fn_return_variable.into());
                postcondition.push(expr.set_default_pos(res_value_range_pos));
            }
            for (formal_arg, local) in formal_args.iter().zip(self.args_iter()) {
                let typ = self.get_local_ty(local);
                if let ty::TyKind::Uint(_) = typ.skip_binder().kind() {
                    precondition.push(vir::Expr::le_cmp(0u32.into(), formal_arg.into()));
                }
            }
        }

        debug_assert!(
            !postcondition.iter().any(|p| p.pos().is_default()),
            "Some postcondition has no position: {:?}",
            postcondition
        );

        let type_arguments = self.encode_type_arguments()?;

        let mut function = vir::Function {
            name: function_name,
            type_arguments,
            formal_args,
            return_type,
            pres: precondition,
            posts: postcondition,
            body,
        };

        self.encoder
            .log_vir_program_before_foldunfold(function.to_string());

        if config::simplify_encoding() {
            function = Simplifier::simplify(function);
        }

        // Patch snapshots
        function = self
            .encoder
            .patch_snapshots_function(function)
            .with_span(self.span)?;

        // Fix arguments
        if let Some(body) = function.body.take() {
            function.body = Some(self.fix_arguments(body)?);
        }

        // Add folding/unfolding
        Ok(function)
    }

    fn fix_arguments(&self, mut expr: vir::Expr) -> SpannedEncodingResult<vir::Expr> {
        for arg in self.args_iter() {
            let arg_ty = self.get_local_ty(arg);
            let span = self.get_local_span(arg);
            let target_place = self
                .encoder
                .encode_value_expr(
                    vir::Expr::local(self.encode_mir_local(arg)?),
                    arg_ty.skip_binder(),
                )
                .with_span(span)?;
            let mut new_place: vir::Expr = self.encode_local(arg)?.into();
            if let ty::TyKind::Ref(_, _, _) = arg_ty.skip_binder().kind() {
                // patch references with an explicit snap app
                // TODO: this probably needs to be adjusted when snapshots of
                //       references are implemented
                new_place = vir::Expr::snap_app(new_place);
            }
            expr = expr.replace_place(&target_place, &new_place);
        }
        Ok(expr)
    }

    fn args_iter(&self) -> impl Iterator<Item = mir::Local> {
        (0..self.sig.skip_binder().inputs().len()).map(|idx| mir::Local::from_usize(1 + idx))
    }

    /// Encode the precondition with two expressions:
    /// - one for the type encoding
    /// - one for the functional specification.
    fn encode_precondition_expr(
        &self,
        contract: &ProcedureContract<'tcx>,
    ) -> SpannedEncodingResult<(vir::Expr, vir::Expr)> {
        let mut type_spec = vec![];
        for &local in contract.args.iter() {
            let local_ty = self.get_local_ty(local.into());
            let fraction = if let ty::TyKind::Ref(_, _, hir::Mutability::Not) =
                local_ty.skip_binder().kind()
            {
                vir::PermAmount::Read
            } else {
                vir::PermAmount::Write
            };
            let opt_pred_perm =
                vir::Expr::pred_permission(self.encode_local(local.into())?.into(), fraction);
            if let Some(spec) = opt_pred_perm {
                type_spec.push(spec)
            }
        }
        let mut func_spec: Vec<vir::Expr> = vec![];

        // Encode functional specification
        let encoded_args: Vec<vir::Expr> = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()).map(|l| l.into()))
            .collect::<Result<_, _>>()?;
        for (assertion, assertion_substs) in
            contract.functional_precondition(self.encoder.env(), self.substs)
        {
            debug!("Encode spec item: {:?}", assertion);
            let encoded_assertion = self.encoder.encode_assertion(
                &assertion,
                None,
                &encoded_args,
                None,
                true,
                self.parent_def_id,
                assertion_substs,
            )?;
            self.encoder
                .error_manager()
                .set_error(encoded_assertion.pos(), ErrorCtxt::PureFunctionDefinition);
            func_spec.push(encoded_assertion);
        }

        Ok((
            type_spec.into_iter().conjoin(),
            func_spec.into_iter().conjoin(),
        ))
    }

    /// Encode the postcondition with one expression just for the functional specification (no
    /// type encoding).
    fn encode_postcondition_expr(
        &self,
        contract: &ProcedureContract<'tcx>,
    ) -> SpannedEncodingResult<vir::Expr> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        // Encode functional specification
        let encoded_args: Vec<vir::Expr> = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()).map(|l| l.into()))
            .collect::<Result<_, _>>()?;
        let encoded_return = self.encode_local(contract.returned_value.into())?;
        debug!("encoded_return: {:?}", encoded_return);

        for (assertion, assertion_substs) in
            contract.functional_postcondition(self.encoder.env(), self.substs)
        {
            let encoded_postcond = self.encoder.encode_assertion(
                &assertion,
                None,
                &encoded_args,
                Some(&encoded_return.clone().into()),
                true,
                self.parent_def_id,
                assertion_substs,
            )?;
            self.encoder
                .error_manager()
                .set_error(encoded_postcond.pos(), ErrorCtxt::PureFunctionDefinition);
            func_spec.push(encoded_postcond);
        }

        let post = func_spec.into_iter().conjoin();

        // TODO: use a better span
        let postcondition_pos = self.encoder.error_manager().register_error(
            self.span,
            ErrorCtxt::PureFunctionDefinition,
            self.parent_def_id,
        );

        // Fix return variable
        let pure_fn_return_variable =
            vir_local! { __result: {self.encode_function_return_type()?} };
        let post = post
            .replace_place(&encoded_return.into(), &pure_fn_return_variable.into())
            .set_default_pos(postcondition_pos);

        Ok(post)
    }

    /// Encodes a VIR local with a snapshot type.
    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = format!("{:?}", local);
        let var_span = self.get_local_span(local);
        let var_type = self
            .encoder
            .encode_snapshot_type(self.get_local_ty(local).skip_binder())
            .with_span(var_span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }

    /// Encodes a VIR local with the original MIR type.
    fn encode_mir_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = format!("{:?}", local);
        let var_span = self.get_local_span(local);
        let var_type = self
            .encoder
            .encode_type(self.get_local_ty(local).skip_binder())
            .with_span(var_span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
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

    pub fn encode_function_name(&self) -> String {
        self.encoder.encode_item_name(self.proc_def_id)
    }

    pub fn encode_function_return_type(&self) -> SpannedEncodingResult<vir::Type> {
        let ty = self.sig.output();

        // Return an error for unsupported return types
        let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
        if !self.encoder.env().type_is_copy(ty, param_env) {
            return Err(SpannedEncodingError::incorrect(
                "return type of pure function does not implement Copy",
                self.get_return_span(),
            ));
        }

        self.encoder
            .encode_snapshot_type(ty.skip_binder())
            .with_span(self.get_return_span())
    }

    fn encode_type_arguments(&self) -> SpannedEncodingResult<Vec<vir::Type>> {
        self.encoder
            .encode_generic_arguments(self.proc_def_id, self.substs)
            .with_span(self.span)
    }

    fn encode_formal_args(&self) -> SpannedEncodingResult<Vec<vir::LocalVar>> {
        let mut formal_args = vec![];
        for local_idx in 0..self.sig.skip_binder().inputs().len() {
            let local_ty = self.sig.input(local_idx);
            let local = prusti_rustc_interface::middle::mir::Local::from_usize(local_idx + 1);
            let var_name = format!("{:?}", local);
            let var_span = self.get_local_span(local);

            let param_env = self.encoder.env().tcx().param_env(self.proc_def_id);
            if !self.encoder.env().type_is_copy(local_ty, param_env) {
                return Err(SpannedEncodingError::incorrect(
                    "pure function parameters must be Copy",
                    var_span,
                ));
            }

            let var_type = self
                .encoder
                .encode_snapshot_type(local_ty.skip_binder())
                .with_span(var_span)?;
            formal_args.push(vir::LocalVar::new(var_name, var_type))
        }
        Ok(formal_args)
    }

    pub fn encode_function_call_info(&self) -> SpannedEncodingResult<FunctionCallInfo> {
        Ok(FunctionCallInfo {
            name: self.encode_function_name(),
            type_arguments: self.encode_type_arguments()?,
            formal_args: self.encode_formal_args()?,
            return_type: self.encode_function_return_type()?,
        })
    }
}

pub(super) struct FunctionCallInfo {
    pub name: String,
    pub type_arguments: Vec<vir::Type>,
    pub formal_args: Vec<vir::LocalVar>,
    pub return_type: vir::Type,
}

impl WithIdentifier for FunctionCallInfo {
    fn get_identifier(&self) -> String {
        vir::compute_identifier(
            &self.name,
            &self.type_arguments,
            &self.formal_args,
            &self.return_type,
        )
    }
}

pub(super) struct FunctionCallInfoHigh {
    pub name: String,
    pub type_arguments: Vec<vir_high::Type>,
    pub return_type: vir_high::Type,
}

impl WithIdentifier for FunctionCallInfoHigh {
    fn get_identifier(&self) -> String {
        compute_function_identifier(&self.name, &self.type_arguments)
    }
}
