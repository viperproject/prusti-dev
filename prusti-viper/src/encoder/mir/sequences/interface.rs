use super::encoder::encode_sequence_types;
use crate::encoder::{
    builtin_encoder::BuiltinFunctionKind, errors::EncodingResult,
    high::builtin_functions::HighBuiltinFunctionEncoderInterface, Encoder,
};
use prusti_common::vir_local;
use prusti_rustc_interface::middle::ty;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use vir_crate::polymorphic as vir;

#[derive(Default)]
pub(crate) struct MirSequencesEncoderState<'tcx> {
    sequence_types_cache: RefCell<FxHashMap<ty::TyKind<'tcx>, EncodedSequenceTypes<'tcx>>>,
}

/// The result of `encode_sequence_types`. Contains types, type predicates
/// and length (if array) of the given sequence type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct EncodedSequenceTypes<'tcx> {
    /// Array/slice type, e.g. `TypedRef(Array$3$i32)`
    pub sequence_pred_type: vir::Type,
    /// Element type, e.g. `TypedRef(i32)`
    pub elem_pred_type: vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
    /// The length of the array, e.g. `3`, for slices this is `None`
    pub sequence_len: Option<usize>,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedSequenceTypes<'tcx> {
    pub fn encode_lookup_pure_call(
        &self,
        encoder: &'p Encoder<'v, 'tcx>,
        seq: vir::Expr,
        idx: vir::Expr,
        ret_ty: vir::Type,
    ) -> vir::Expr {
        let (lookup_pure, type_arguments) = if let Some(len) = self.sequence_len {
            encoder.encode_builtin_function_use(BuiltinFunctionKind::ArrayLookupPure {
                array_pred_type: self.sequence_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
                array_len: len,
                return_ty: ret_ty.clone(),
            })
        } else {
            encoder.encode_builtin_function_use(BuiltinFunctionKind::SliceLookupPure {
                slice_pred_type: self.sequence_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
                return_ty: ret_ty.clone(),
            })
        };
        vir::Expr::func_app(
            lookup_pure,
            type_arguments,
            vec![seq, idx],
            vec![
                vir_local! { self: {self.sequence_pred_type.clone()} },
                vir_local! { idx: Int },
            ],
            ret_ty,
            vir::Position::default(),
        )
    }

    pub fn len(&self, encoder: &'p Encoder<'v, 'tcx>, sequence: vir::Expr) -> vir::Expr {
        if let Some(len) = self.sequence_len {
            return vir::Expr::from(len);
        }

        let (slice_len, type_arguments) =
            encoder.encode_builtin_function_use(BuiltinFunctionKind::SliceLen {
                slice_pred_type: self.sequence_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
            });
        vir::Expr::func_app(
            slice_len,
            type_arguments,
            vec![sequence],
            vec![vir_local! { self: {self.sequence_pred_type.clone()} }],
            vir::Type::Int,
            vir::Position::default(),
        )
    }
}

pub(crate) trait MirSequencesEncoderInterface<'tcx> {
    fn encode_sequence_types(
        &self,
        sequence_ty: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedSequenceTypes<'tcx>>;
}

impl<'v, 'tcx: 'v> MirSequencesEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_sequence_types(
        &self,
        sequence_ty: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedSequenceTypes<'tcx>> {
        if !self
            .mir_sequences_encoder_state
            .sequence_types_cache
            .borrow()
            .contains_key(sequence_ty.kind())
        {
            let encoded_type = encode_sequence_types(self, sequence_ty)?;
            assert!(self
                .mir_sequences_encoder_state
                .sequence_types_cache
                .borrow_mut()
                .insert(sequence_ty.kind().clone(), encoded_type.clone())
                .is_none());
        }
        let encoded_type = self
            .mir_sequences_encoder_state
            .sequence_types_cache
            .borrow()[sequence_ty.kind()]
        .clone();
        Ok(encoded_type)
    }
}
