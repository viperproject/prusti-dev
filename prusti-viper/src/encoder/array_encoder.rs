// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty;
use rustc_hash::{FxHashMap};
use std::convert::TryInto;
use crate::encoder::{
    Encoder,
    errors::{EncodingResult, EncodingError},
    builtin_encoder::BuiltinFunctionKind,
};
use prusti_common::vir_local;
use vir_crate::polymorphic as vir;


use super::high::{types::HighTypeEncoderInterface, builtin_functions::HighBuiltinFunctionEncoderInterface};


/// The result of `ArrayEncoder::encode_sequence_types`. Contains types, type predicates and length (if array) of the given sequence type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct EncodedSequenceTypes<'tcx> {
    /// Array/Slice type, e.g. TypedRef(Array$3$i32)
    pub sequence_pred_type: vir::Type,
    /// Element type, e.g. TypedRef(i32)
    pub elem_pred_type: vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
    /// The length of the array, e.g. 3, for slices this is None
    pub sequence_len: Option<usize>,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedSequenceTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, encoder: &'p Encoder<'v, 'tcx>, seq: vir::Expr, idx: vir::Expr, ret_ty: vir::Type) -> vir::Expr {
        let (lookup_pure, type_arguments) = if let Some(len) = self.sequence_len {
            encoder.encode_builtin_function_use(
                BuiltinFunctionKind::ArrayLookupPure {
                    array_pred_type: self.sequence_pred_type.clone(),
                    elem_pred_type: self.elem_pred_type.clone(),
                    array_len: len,
                    return_ty: ret_ty.clone(),
                }
            )
        } else {
            encoder.encode_builtin_function_use(
                BuiltinFunctionKind::SliceLookupPure {
                    slice_pred_type: self.sequence_pred_type.clone(),
                    elem_pred_type: self.elem_pred_type.clone(),
                    return_ty: ret_ty.clone(),
                }
            )
        };
        vir::Expr::func_app(
            lookup_pure,
            type_arguments,
            vec![
                seq,
                idx,
            ],
            vec![
                vir_local!{ self: {self.sequence_pred_type.clone()} },
                vir_local!{ idx: Int },
            ],
            ret_ty,
            vir::Position::default(),
        )
    }
    pub fn len(&self, encoder: &'p Encoder<'v, 'tcx>, sequence: vir::Expr) -> vir::Expr {
        if let Some(len) = self.sequence_len {
            return vir::Expr::from(len);
        }

        let (slice_len, type_arguments) = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLen {
                slice_pred_type: self.sequence_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
            }
        );
        vir::Expr::func_app(
            slice_len,
            type_arguments,
            vec![
                sequence,
            ],
            vec![
                vir_local!{ self: {self.sequence_pred_type.clone()} },
            ],
            vir::Type::Int,
            vir::Position::default(),
        )
    }
}



pub struct SequenceTypesEncoder<'tcx> {
    sequence_types_cache: FxHashMap<ty::Ty<'tcx>, EncodedSequenceTypes<'tcx>>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SequenceTypesEncoder<'tcx> {
    pub fn new() -> Self {
        SequenceTypesEncoder {
            sequence_types_cache: FxHashMap::default(),
        }
    }

    pub fn encode_sequence_types(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        sequence_ty_rs: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedSequenceTypes<'tcx>> {
        if let Some(cached) = self.sequence_types_cache.get(&sequence_ty_rs) {
            return Ok(cached.clone());
        }

        let (elem_ty_rs, sequence_len) = match sequence_ty_rs.kind() {
            ty::TyKind::Array(elem_ty, array_len) => {
                let len = encoder.const_eval_intlike(array_len.val())?.to_u64().unwrap().try_into().unwrap();
                (*elem_ty, Some(len))
            }
            ty::TyKind::Slice(elem_ty) => (*elem_ty, None),
            ty::TyKind::Str => return Err(
                EncodingError::unsupported("Encoding of Str slice type".to_string())
            ),
            _ => unreachable!(),
        };

        let sequence_pred_type = encoder.encode_type(sequence_ty_rs)?;
        let elem_pred_type = encoder.encode_type(elem_ty_rs)?;

        let encoded = EncodedSequenceTypes {
            sequence_pred_type,
            elem_pred_type,
            elem_ty_rs,
            sequence_len,
        };
        self.sequence_types_cache.insert(sequence_ty_rs, encoded.clone());

        Ok(encoded)
    }
}
