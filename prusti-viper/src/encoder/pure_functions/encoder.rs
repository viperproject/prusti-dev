// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{super::encoder::SubstMap, interpreter::PureFunctionBackwardInterpreter};
use crate::encoder::{
    borrows::{compute_procedure_contract, ProcedureContract},
    builtin_encoder::BuiltinFunctionKind,
    errors::{
        EncodingError, EncodingResult, ErrorCtxt, PanicCause, SpannedEncodingError,
        SpannedEncodingResult, WithSpan,
    },
    foldunfold,
    mir_encoder::{MirEncoder, PlaceEncoder, PlaceEncoding, PRECONDITION_LABEL, WAND_LHS_LABEL},
    mir_interpreter::{
        run_backward_interpretation, BackwardMirInterpreter, MultiExprBackwardInterpreterState,
    },
    snapshot, Encoder,
};
use log::{debug, trace};
use prusti_common::{config, vir::optimizations::functions::Simplifier, vir_local};
use prusti_interface::{specs::typed, PrustiError};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use rustc_span::Span;
use std::{collections::HashMap, mem};
use vir_crate::polymorphic::{self as vir, ExprIterator};

pub(super) struct PureFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Body<'tcx>,
    interpreter: PureFunctionBackwardInterpreter<'p, 'v, 'tcx>,
    parent_def_id: DefId,
    tymap: &'p SubstMap<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> PureFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        proc_def_id: DefId,
        mir: &'p mir::Body<'tcx>,
        is_encoding_assertion: bool,
        parent_def_id: DefId,
        tymap: &'p SubstMap<'tcx>,
    ) -> Self {
        trace!("PureFunctionEncoder constructor: {:?}", proc_def_id);
        let interpreter = PureFunctionBackwardInterpreter::new(
            encoder,
            mir,
            proc_def_id,
            is_encoding_assertion,
            parent_def_id,
            tymap.clone(),
        );
        PureFunctionEncoder {
            encoder,
            proc_def_id,
            mir,
            interpreter,
            parent_def_id,
            tymap,
        }
    }

    /// Used to encode expressions in assertions
    pub fn encode_body(&self) -> SpannedEncodingResult<vir::Expr> {
        let function_name = self.encoder.env().get_absolute_item_name(self.proc_def_id);
        debug!("Encode body of pure function {}", function_name);

        let state = run_backward_interpretation(self.mir, &self.interpreter)?
            .unwrap_or_else(|| panic!("Procedure {:?} contains a loop", self.proc_def_id));
        let body_expr = state.into_expressions().remove(0);
        debug!(
            "Pure function {} has been encoded with expr: {}",
            function_name, body_expr
        );
        let substs = &self
            .encoder
            .type_substitution_polymorphic_type_map(self.tymap)
            .with_span(self.mir.span)?;
        let patched_body_expr = body_expr.patch_types(substs);
        Ok(patched_body_expr)
    }

    pub fn encode_function(&self) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        debug!("Encode pure function {}", function_name);
        let mut state = run_backward_interpretation(self.mir, &self.interpreter)?
            .unwrap_or_else(|| panic!("Procedure {:?} contains a loop", self.proc_def_id));

        // Fix arguments
        for arg in self.mir.args_iter() {
            let arg_ty = self.interpreter.mir_encoder().get_local_ty(arg);
            let span = self.get_local_span(arg);
            let target_place = self
                .encoder
                .encode_value_expr(
                    vir::Expr::local(self.interpreter.mir_encoder().encode_local(arg)?),
                    arg_ty,
                )
                .with_span(span)?;
            let new_place: vir::Expr = self.encode_local(arg)?.into();
            state.substitute_place(&target_place, new_place);
        }

        let mut body_expr = state.into_expressions().remove(0);
        debug!(
            "Pure function {} has been encoded with expr: {}",
            function_name, body_expr
        );

        // if the function returns a snapshot, we take a snapshot of the body
        if self.encode_function_return_type()?.is_snapshot() {
            let ty = self
                .encoder
                .resolve_typaram(self.mir.return_ty(), self.tymap);
            let return_span = self.get_local_span(mir::RETURN_PLACE);

            if !self.encoder.env().type_is_copy(ty) {
                return Err(SpannedEncodingError::unsupported(
                    "return type of pure function does not implement Copy",
                    return_span,
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
        predicate_body: &typed::Assertion<'tcx>,
    ) -> SpannedEncodingResult<vir::Function> {
        let function_name = self.encode_function_name();
        debug!("Encode predicate function {}", function_name);

        let mir_span = self.encoder.env().tcx().def_span(self.proc_def_id);
        let contract = self
            .encoder
            .get_procedure_contract_for_def(self.proc_def_id)
            .with_span(mir_span)?;
        let encoded_args = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()).map(|l| l.into()))
            .collect::<Result<Vec<_>, _>>()?;

        let predicate_body_encoded = self.encoder.encode_assertion(
            predicate_body,
            self.mir,
            None,
            &encoded_args,
            None,
            true,
            None,
            ErrorCtxt::GenericExpression,
            self.parent_def_id,
            self.tymap,
        )?;

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
            .get_procedure_contract_for_def(self.proc_def_id)
            .with_span(self.mir.span)?;
        let substs = &self
            .encoder
            .type_substitution_polymorphic_type_map(self.tymap)
            .with_span(self.mir.span)?;

        let (type_precondition, func_precondition) = self.encode_precondition_expr(&contract)?;
        let patched_type_precondition = type_precondition.patch_types(substs);

        let mut precondition = vec![patched_type_precondition, func_precondition];
        let mut postcondition = vec![self.encode_postcondition_expr(&contract)?];

        let mut formal_args = vec![];
        for local in self.mir.args_iter() {
            let mir_encoder = self.interpreter.mir_encoder();
            let var_name = mir_encoder.encode_local_var_name(local);
            let var_span = mir_encoder.get_local_span(local);
            let mir_type = mir_encoder.get_local_ty(local);
            if !self.encoder.env().type_is_copy(mir_type) {
                return Err(SpannedEncodingError::incorrect(
                    "pure function parameters must be Copy",
                    var_span,
                ));
            }
            let var_type = self
                .encoder
                .encode_snapshot_type(mir_type, self.tymap)
                .with_span(var_span)?;
            let var_type = var_type.patch(substs);
            formal_args.push(vir::LocalVar::new(var_name, var_type))
        }
        let return_type = self.encode_function_return_type()?;

        let res_value_range_pos = self.encoder.error_manager().register(
            self.mir.span,
            ErrorCtxt::PureFunctionPostconditionValueRangeOfResult,
            self.parent_def_id,
        );
        let pure_fn_return_variable = vir_local! { __result: {return_type.clone()} };
        // Add value range of the arguments and return value to the pre/postconditions
        if config::check_overflows() {
            let return_bounds: Vec<_> = self
                .encoder
                .encode_type_bounds(
                    &vir::Expr::local(pure_fn_return_variable),
                    self.mir.return_ty(),
                )
                .into_iter()
                .map(|p| p.set_default_pos(res_value_range_pos))
                .collect();
            postcondition.extend(return_bounds);

            for (formal_arg, local) in formal_args.iter().zip(self.mir.args_iter()) {
                let typ = self.interpreter.mir_encoder().get_local_ty(local);
                let bounds = self
                    .encoder
                    .encode_type_bounds(&vir::Expr::local(formal_arg.clone()), typ);
                precondition.extend(bounds);
            }
        } else if config::encode_unsigned_num_constraint() {
            if let ty::TyKind::Uint(_) = self.mir.return_ty().kind() {
                let expr = vir::Expr::le_cmp(0.into(), pure_fn_return_variable.into());
                postcondition.push(expr.set_default_pos(res_value_range_pos));
            }
            for (formal_arg, local) in formal_args.iter().zip(self.mir.args_iter()) {
                let typ = self.interpreter.mir_encoder().get_local_ty(local);
                if let ty::TyKind::Uint(_) = typ.kind() {
                    precondition.push(vir::Expr::le_cmp(0.into(), formal_arg.into()));
                }
            }
        }

        debug_assert!(
            !postcondition.iter().any(|p| p.pos().is_default()),
            "Some postcondition has no position: {:?}",
            postcondition
        );

        let mut function = vir::Function {
            name: function_name,
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
            .patch_snapshots_function(function, self.tymap)
            .with_span(self.mir.span)?;

        // Add folding/unfolding
        Ok(function)
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
            let local_ty = self.interpreter.mir_encoder().get_local_ty(local.into());
            let fraction = if let ty::TyKind::Ref(_, _, hir::Mutability::Not) = local_ty.kind() {
                vir::PermAmount::Read
            } else {
                vir::PermAmount::Write
            };
            let opt_pred_perm = self
                .interpreter
                .mir_encoder()
                .encode_place_predicate_permission(
                    self.encode_local(local.into())?.into(),
                    fraction,
                );
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
        for item in contract.functional_precondition() {
            debug!("Encode spec item: {:?}", item);
            func_spec.push(self.encoder.encode_assertion(
                item,
                self.mir,
                None,
                &encoded_args,
                None,
                true,
                None,
                ErrorCtxt::GenericExpression,
                self.parent_def_id,
                self.tymap,
            )?);
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

        for item in contract.functional_postcondition() {
            let encoded_postcond = self.encoder.encode_assertion(
                item,
                self.mir,
                None,
                &encoded_args,
                Some(&encoded_return.clone().into()),
                true,
                None,
                ErrorCtxt::GenericExpression,
                self.parent_def_id,
                self.tymap,
            )?;
            debug_assert!(!encoded_postcond.pos().is_default());
            func_spec.push(encoded_postcond);
        }

        let post = func_spec.into_iter().conjoin();

        // TODO: use a better span
        let postcondition_pos = self.encoder.error_manager().register(
            self.mir.span,
            ErrorCtxt::GenericExpression,
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

    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let mir_encoder = self.interpreter.mir_encoder();
        let var_name = mir_encoder.encode_local_var_name(local);
        let var_span = mir_encoder.get_local_span(local);
        let var_type = self
            .encoder
            .encode_snapshot_type(
                self.interpreter.mir_encoder().get_local_ty(local),
                self.tymap,
            )
            .with_span(var_span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }

    fn get_local_span(&self, local: mir::Local) -> Span {
        self.interpreter.mir_encoder().get_local_span(local)
    }

    pub fn encode_function_name(&self) -> String {
        self.encoder.encode_item_name(self.proc_def_id)
    }

    pub fn encode_function_return_type(&self) -> SpannedEncodingResult<vir::Type> {
        let ty = self
            .encoder
            .resolve_typaram(self.mir.return_ty(), self.tymap);
        let return_span = self.get_local_span(mir::RETURN_PLACE);

        // Return an error for unsupported return types
        if !self.encoder.env().type_is_copy(ty) {
            return Err(SpannedEncodingError::incorrect(
                "return type of pure function does not implement Copy",
                return_span,
            ));
        }

        let return_local = mir::Place::return_place().as_local().unwrap();
        let span = self.interpreter.mir_encoder().get_local_span(return_local);
        self.encoder
            .encode_snapshot_type(ty, self.tymap)
            .with_span(span)
    }
}
