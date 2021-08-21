// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty;
use std::{
    collections::HashMap,
    convert::TryInto,
};
use crate::encoder::{
    Encoder,
    errors::EncodingResult,
    builtin_encoder::BuiltinFunctionKind,
};
use vir_crate::{vir_local, vir_type};
use vir_crate::polymorphic as polymorphic_vir;


/// The result of `ArrayEncoder::encode_array_types`. Contains types, type predicates and length of the given array type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct EncodedArrayTypes<'tcx> {
    /// Array type, e.g. TypedRef(Array$3$i32)
    pub array_pred_type: polymorphic_vir::Type,
    /// Element type, e.g. TypedRef(i32)
    pub elem_pred_type: polymorphic_vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
    /// The length of the array, e.g. 3
    pub array_len: usize,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedArrayTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, encoder: &'p Encoder<'v, 'tcx>, array: polymorphic_vir::Expr, idx: polymorphic_vir::Expr, ret_ty: polymorphic_vir::Type) -> polymorphic_vir::Expr {
        let lookup_pure = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::ArrayLookupPure {
                array_pred_type: self.array_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
                array_len: self.array_len,
                return_ty: ret_ty.clone(),
            }
        );

        polymorphic_vir::Expr::func_app(
            lookup_pure,
            vec![
                array,
                idx,
            ],
            vec![
                vir_local!{ self: {self.array_pred_type.clone()} },
                vir_local!{ idx: Int },
            ],
            ret_ty,
            polymorphic_vir::Position::default(),
        )
    }
}

/// The result of `ArrayEncoder::encode_slice_types`. Contains types and type predicates of the given array type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct EncodedSliceTypes<'tcx> {
    /// Slice type, e.g. TypedRef(Slice$i32)
    pub slice_pred_type: polymorphic_vir::Type,
    /// Element type, e.g. TypedRef(i32)
    pub elem_pred_type: polymorphic_vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedSliceTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, encoder: &'p Encoder<'v, 'tcx>, slice: polymorphic_vir::Expr, idx: polymorphic_vir::Expr, ret_ty: polymorphic_vir::Type) -> polymorphic_vir::Expr {
        let lookup_pure = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLookupPure {
                slice_pred_type: self.slice_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
                return_ty: ret_ty.clone(),
            }
        );

        polymorphic_vir::Expr::func_app( 
            lookup_pure,
            vec![
                slice,
                idx,
            ],
            vec![
                vir_local!{ self: {self.slice_pred_type.clone()} },
                vir_local!{ idx: Int },
            ],
            ret_ty,
            polymorphic_vir::Position::default(),
        )
    }

    pub fn encode_slice_len_call(&self, encoder: &'p Encoder<'v, 'tcx>, slice: polymorphic_vir::Expr) -> polymorphic_vir::Expr {
        let slice_len = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLen {
                slice_pred_type: self.slice_pred_type.clone(),
                elem_pred_type: self.elem_pred_type.clone(),
            }
        );

        polymorphic_vir::Expr::func_app(
            slice_len,
            vec![
                slice,
            ],
            vec![
                vir_local!{ self: {self.slice_pred_type.clone()} },
            ],
            polymorphic_vir::Type::Int,
            polymorphic_vir::Position::default(),
        )
    }
}



pub struct ArrayTypesEncoder<'tcx> {
    array_types_cache: HashMap<ty::Ty<'tcx>, EncodedArrayTypes<'tcx>>,
    slice_types_cache: HashMap<ty::Ty<'tcx>, EncodedSliceTypes<'tcx>>,
}

impl<'p, 'v: 'p, 'tcx: 'v> ArrayTypesEncoder<'tcx> {
    pub fn new() -> Self {
        ArrayTypesEncoder {
            array_types_cache: HashMap::new(),
            slice_types_cache: HashMap::new(),
        }
    }

    /// Encode types, type predicates and builtin lookup functions required for handling slices of
    /// type `slice_ty`.
    pub fn encode_slice_types(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        slice_ty_rs: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedSliceTypes<'tcx>> {
        if let Some(cached) = self.slice_types_cache.get(&slice_ty_rs) {
            return Ok(cached.clone());
        }

        let slice_pred_type = encoder.encode_type(slice_ty_rs)?;
        let elem_ty_rs = if let ty::TyKind::Slice(elem_ty) = slice_ty_rs.kind() {
            elem_ty
        } else {
            unreachable!()
        };

        let elem_pred_type = encoder.encode_type(elem_ty_rs)?;

        let encoded = EncodedSliceTypes {
            slice_pred_type,
            elem_pred_type,
            elem_ty_rs,
        };
        self.slice_types_cache.insert(&slice_ty_rs, encoded.clone());

        Ok(encoded)
    }

    /// Encode types, type predicates and builtin lookup functions required for handling arrays of
    /// type `array_ty`.
    pub fn encode_array_types(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        array_ty_rs: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedArrayTypes<'tcx>> {
        if let Some(cached) = self.array_types_cache.get(&array_ty_rs) {
            return Ok(cached.clone());
        }

        // type predicates
        let (elem_ty_rs, len) = if let ty::TyKind::Array(elem_ty, len) = array_ty_rs.kind() {
            (elem_ty, len)
        } else {
            unreachable!()
        };

        // types
        let array_pred_type = encoder.encode_type(array_ty_rs)?;
        let elem_pred_type = encoder.encode_type(elem_ty_rs)?;

        let array_len = encoder.const_eval_intlike(&len.val)?
            .to_u64().unwrap().try_into().unwrap();

        let encoded = EncodedArrayTypes {
            array_pred_type,
            elem_pred_type,
            elem_ty_rs,
            array_len,
        };
        self.array_types_cache.insert(&array_ty_rs, encoded.clone());

        Ok(encoded)
    }
}
