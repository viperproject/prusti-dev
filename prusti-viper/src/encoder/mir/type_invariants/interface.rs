use super::encoder::{encode_invariant_def, encode_twostate_invariant_expr, encode_invariant_stub, needs_invariant_func, encode_twostate_invariant_reflexivity_expr};
use crate::encoder::errors::EncodingResult;
use prusti_common::config;
use prusti_rustc_interface::middle::ty;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use vir_crate::polymorphic::{self as vir};

#[derive(Default)]
pub(crate) struct TypeInvariantEncoderState<'tcx> {
    encoded_invariants: RefCell<FxHashMap<ty::TyKind<'tcx>, vir::Function>>
}

pub(crate) trait TypeInvariantEncoderInterface<'tcx> {
    // TODO(inv): rename to ..._type_invariant_...
    fn encode_invariant_func_app(
        &self,
        ty: ty::Ty<'tcx>,
        encoded_arg: vir::Expr,
    ) -> EncodingResult<vir::Expr>;

    fn encode_twostate_invariant(
        &self,
        pre_label: Option<&str>,
        ty: ty::Ty<'tcx>,
        encoded_arg: vir::Expr,
    ) -> EncodingResult<vir::Expr>;

    fn encode_twostate_invariant_reflexivity_expr(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr>;
}

impl<'v, 'tcx: 'v> TypeInvariantEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {

    fn encode_twostate_invariant_reflexivity_expr(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        // match snapshot ref/box peeling
        let ty = crate::encoder::snapshot::encoder::strip_refs_and_boxes(ty);

        let ty = self.env().tcx().erase_regions_ty(ty);

        if !needs_invariant_func(ty) {
            return Ok(true.into());
        }
        encode_twostate_invariant_reflexivity_expr(self, ty)
    }

    fn encode_twostate_invariant(
        &self,
        pre_label: Option<&str>,
        ty: ty::Ty<'tcx>,
        encoded_arg: vir::Expr,
    ) -> EncodingResult<vir::Expr> {
        // match snapshot ref/box peeling
        let ty = crate::encoder::snapshot::encoder::strip_refs_and_boxes(ty);

        let ty = self.env().tcx().erase_regions_ty(ty);

        if !needs_invariant_func(ty) {
            return Ok(true.into());
        }
        encode_twostate_invariant_expr(pre_label, self, ty, encoded_arg)
    }

    fn encode_invariant_func_app(
        &self,
        ty: ty::Ty<'tcx>,
        encoded_arg: vir::Expr,
    ) -> EncodingResult<vir::Expr> {
        if !config::enable_type_invariants() {
            return Ok(true.into());
        }

        // match snapshot ref/box peeling
        let ty = crate::encoder::snapshot::encoder::strip_refs_and_boxes(ty);

        let ty = self.env().tcx().erase_regions_ty(ty);

        if !needs_invariant_func(ty) {
            return Ok(true.into());
        }

        if let Some(encoded) = self
            .type_invariant_encoder_state
            .encoded_invariants
            .borrow()
            .get(ty.kind())
        {
            return Ok(encoded.clone().apply(vec![encoded_arg]));
        }

        // handle recursive definitions by inserting a bodyless stub
        self.type_invariant_encoder_state
            .encoded_invariants
            .borrow_mut()
            .insert(ty.kind().clone(), encode_invariant_stub(self, ty)?);

        let encoded = encode_invariant_def(self, ty)?;
        // TODO: clean up stub if encoding fails?

        // replace the stub with the full function
        self.type_invariant_encoder_state
            .encoded_invariants
            .borrow_mut()
            .insert(ty.kind().clone(), encoded.clone());

        Ok(encoded.apply(vec![encoded_arg]))
    }
}
