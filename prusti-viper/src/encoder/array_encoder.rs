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
use prusti_common::{
    vir,
};
use vir_crate::{vir_local, vir_type};
use vir_crate::polymorphic as polymorphic_vir;


/// The result of `ArrayEncoder::encode_array_types`. Contains types, type predicates and length of the given array type.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct EncodedArrayTypes<'tcx> {
    /// String to use as type predicate, e.g. Array$3$i32
    pub array_pred: String,
    /// Array type, e.g. TypedRef(Array$3$i32)
    pub array_ty: polymorphic_vir::Type,
    /// String to use as type predicate for the element type, e.g. i32
    pub elem_pred: String,
    /// Element type, e.g. TypedRef(i32)
    pub elem_ty: polymorphic_vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
    /// The length of the array, e.g. 3
    pub array_len: usize,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedArrayTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, encoder: &'p Encoder<'v, 'tcx>, array: polymorphic_vir::Expr, idx: polymorphic_vir::Expr, ret_ty: polymorphic_vir::Type) -> polymorphic_vir::Expr {
        let lookup_pure = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::ArrayLookupPure {
                array_ty_pred: self.array_pred.clone(),
                elem_ty_pred: self.elem_pred.clone(),
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
                vir_local!{ self: {self.array_ty.clone()} },
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
    /// String to use as type predicate, e.g. Slice$i32
    pub slice_pred: String,
    /// Slice type, e.g. TypedRef(Slice$i32)
    pub slice_ty: polymorphic_vir::Type,
    /// String to use as type predicate of the element, e.g. i32
    pub elem_pred: String,
    /// Element type, e.g. TypedRef(i32)
    pub elem_ty: polymorphic_vir::Type,
    /// The non-encoded element type as passed by rustc
    pub elem_ty_rs: ty::Ty<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> EncodedSliceTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, encoder: &'p Encoder<'v, 'tcx>, slice: polymorphic_vir::Expr, idx: polymorphic_vir::Expr, ret_ty: polymorphic_vir::Type) -> polymorphic_vir::Expr {
        let lookup_pure = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLookupPure {
                slice_ty_pred: self.slice_pred.clone(),
                elem_ty_pred: self.elem_pred.clone(),
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
                vir_local!{ self: {self.slice_ty.clone()} },
                vir_local!{ idx: Int },
            ],
            ret_ty,
            polymorphic_vir::Position::default(),
        )
    }

    pub fn encode_slice_len_call(&self, encoder: &'p Encoder<'v, 'tcx>, slice: polymorphic_vir::Expr) -> polymorphic_vir::Expr {
        let slice_len = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLen {
                slice_ty_pred: self.slice_pred.clone(),
                elem_ty_pred: self.elem_pred.clone(),
            }
        );

        polymorphic_vir::Expr::func_app(
            slice_len,
            vec![
                slice,
            ],
            vec![
                vir_local!{ self: {self.slice_ty.clone()} },
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

        let slice_pred = encoder.encode_type_predicate_use(slice_ty_rs)?.encode_as_string();
        let elem_ty_rs = if let ty::TyKind::Slice(elem_ty) = slice_ty_rs.kind() {
            elem_ty
        } else {
            unreachable!()
        };

        let elem_pred = encoder.encode_type_predicate_use(elem_ty_rs)?.encode_as_string();

        let slice_ty = encoder.encode_type(slice_ty_rs)?;
        let elem_ty = encoder.encode_type(elem_ty_rs)?;

        let encoded = EncodedSliceTypes {
            slice_pred,
            slice_ty,
            elem_pred,
            elem_ty,
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
        let array_pred = encoder.encode_type_predicate_use(array_ty_rs)?.encode_as_string();
        let (elem_ty_rs, len) = if let ty::TyKind::Array(elem_ty, len) = array_ty_rs.kind() {
            (elem_ty, len)
        } else {
            unreachable!()
        };
        let elem_pred = encoder.encode_type_predicate_use(elem_ty_rs)?.encode_as_string();

        // types
        let array_ty = encoder.encode_type(array_ty_rs)?;
        let elem_ty = encoder.encode_type(elem_ty_rs)?;

        let array_len = encoder.const_eval_intlike(&len.val)?
            .to_u64().unwrap().try_into().unwrap();

        let encoded = EncodedArrayTypes {
            array_pred,
            array_ty,
            elem_pred,
            elem_ty,
            elem_ty_rs,
            array_len,
        };
        self.array_types_cache.insert(&array_ty_rs, encoded.clone());

        Ok(encoded)
    }
}
