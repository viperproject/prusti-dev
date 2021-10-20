use super::encoder::SnapshotEncoder;
use crate::encoder::{encoder::SubstMap, errors::EncodingResult};
use rustc_middle::{mir, ty};
use std::{cell::RefCell, rc::Rc};
use vir_crate::{high as vir_high, polymorphic as vir_poly};

#[derive(Default)]
pub(crate) struct SnapshotEncoderState {
    encoder: RefCell<SnapshotEncoder>,
}

pub(crate) trait SnapshotEncoderInterface<'tcx> {
    fn get_domain(&self, name: &str) -> vir_poly::Domain;
    fn contains_snapshot_function(&self, identifier: &vir_poly::FunctionIdentifier) -> bool;
    fn get_snapshot_function(
        &self,
        identifier: &vir_poly::FunctionIdentifier,
    ) -> Rc<vir_poly::Function>;
    fn encode_discriminant_postcondition(
        &self,
        expr_self: vir_poly::Expr,
        expr_result: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn patch_snapshots_method(
        &self,
        method: vir_poly::CfgMethod,
    ) -> EncodingResult<vir_poly::CfgMethod>;
    fn patch_snapshots_function(
        &self,
        function: vir_poly::Function,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Function>;
    fn patch_snapshots(
        &self,
        expr: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot_type(
        &self,
        ty: ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Type>;
    fn encode_snapshot_constant(
        &self,
        expr: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
        args: Vec<vir_poly::Expr>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot_array_idx(
        &self,
        ty: ty::Ty<'tcx>,
        array: vir_poly::Expr,
        idx: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot_slice_idx(
        &self,
        ty: ty::Ty<'tcx>,
        slice: vir_poly::Expr,
        idx: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot_slice_len(
        &self,
        ty: ty::Ty<'tcx>,
        slice: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn encode_snapshot_slicing(
        &self,
        base_ty: ty::Ty<'tcx>,
        base: vir_poly::Expr,
        slice_ty: ty::Ty<'tcx>,
        lo: vir_poly::Expr,
        hi: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr>;
    fn supports_snapshot_equality(
        &self,
        ty: ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<bool>;
    fn is_quantifiable(&self, ty: ty::Ty<'tcx>, tymap: &SubstMap<'tcx>) -> EncodingResult<bool>;
}

impl<'v, 'tcx: 'v> SnapshotEncoderInterface<'tcx> for super::super::Encoder<'v, 'tcx> {
    fn get_domain(&self, name: &str) -> vir_poly::Domain {
        if let Some(domain) = self
            .snapshot_encoder_state
            .encoder
            .borrow()
            .get_domain(name)
        {
            domain.clone()
        } else {
            unreachable!("Domain not found: {}", name);
        }
    }
    fn contains_snapshot_function(&self, identifier: &vir_poly::FunctionIdentifier) -> bool {
        self.snapshot_encoder_state
            .encoder
            .borrow()
            .contains_function(identifier)
    }
    fn get_snapshot_function(
        &self,
        identifier: &vir_poly::FunctionIdentifier,
    ) -> Rc<vir_poly::Function> {
        let encoder = self.snapshot_encoder_state.encoder.borrow();
        encoder.get_function(identifier)
    }
    fn encode_discriminant_postcondition(
        &self,
        expr_self: vir_poly::Expr,
        expr_result: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_discriminant_post(self, expr_self, expr_result, tymap)
    }
    fn patch_snapshots_method(
        &self,
        method: vir_poly::CfgMethod,
    ) -> EncodingResult<vir_poly::CfgMethod> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .patch_snapshots_method(self, method)
    }
    fn patch_snapshots_function(
        &self,
        function: vir_poly::Function,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Function> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .patch_snapshots_function(self, function, tymap)
    }
    fn patch_snapshots(
        &self,
        expr: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .patch_snapshots_expr(self, expr, tymap)
    }
    fn encode_snapshot_type(
        &self,
        ty: ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Type> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_type(self, ty, tymap)
    }

    /// Constructs a snapshot of a constant.
    /// The result is not necessarily a domain; it could be a primitive type.
    fn encode_snapshot_constant(
        &self,
        expr: &mir::Constant<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        let args = match expr.ty().kind() {
            ty::TyKind::Tuple(substs) if substs.is_empty() => vec![],
            _ => {
                let const_val = match expr.literal {
                    mir::ConstantKind::Ty(ty::Const { val, .. }) => *val,
                    mir::ConstantKind::Val(val, _) => ty::ConstKind::Value(val),
                };
                vec![self.encode_const_expr(expr.ty(), &const_val)?]
            }
        };
        self.encode_snapshot(expr.ty(), None, args, &SubstMap::new())
    }

    /// Constructs a snapshot. The `variant` is needed only if `ty` is an enum.
    /// The result is not necessarily a domain; it could be a primitive type.
    fn encode_snapshot(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<usize>,
        args: Vec<vir_poly::Expr>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_constructor(self, ty, variant, args, tymap)
    }

    fn encode_snapshot_array_idx(
        &self,
        ty: ty::Ty<'tcx>,
        array: vir_poly::Expr,
        idx: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_array_idx(self, ty, array, idx, tymap)
    }

    fn encode_snapshot_slice_idx(
        &self,
        ty: ty::Ty<'tcx>,
        slice: vir_poly::Expr,
        idx: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_slice_idx(self, ty, slice, idx, tymap)
    }

    fn encode_snapshot_slice_len(
        &self,
        ty: ty::Ty<'tcx>,
        slice: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_slice_len(self, ty, slice, tymap)
    }

    fn encode_snapshot_slicing(
        &self,
        base_ty: ty::Ty<'tcx>,
        base: vir_poly::Expr,
        slice_ty: ty::Ty<'tcx>,
        lo: vir_poly::Expr,
        hi: vir_poly::Expr,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<vir_poly::Expr> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .encode_slicing(self, base_ty, base, slice_ty, lo, hi, tymap)
    }

    fn supports_snapshot_equality(
        &self,
        ty: ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
    ) -> EncodingResult<bool> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .supports_equality(self, ty, tymap)
    }

    fn is_quantifiable(&self, ty: ty::Ty<'tcx>, tymap: &SubstMap<'tcx>) -> EncodingResult<bool> {
        self.snapshot_encoder_state
            .encoder
            .borrow_mut()
            .is_quantifiable(self, ty, tymap)
    }
}
