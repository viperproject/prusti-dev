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
    vir_local,
};


pub struct EncodedArrayTypes<'tcx> {
    pub array_pred: String,
    pub array_ty: vir::Type,
    pub elem_ty: vir::Type,
    pub elem_value_ty: vir::Type,
    pub elem_ty_rs: ty::Ty<'tcx>,
    pub array_len: usize,
    pub lookup_pure_name: String,
}

impl<'tcx> EncodedArrayTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, array: vir::Expr, idx: vir::Expr) -> vir::Expr {
        vir::Expr::func_app(
            self.lookup_pure_name.clone(),
            vec![
                array,
                idx,
            ],
            vec![
                vir_local!{ self: {self.array_ty.clone()} },
                vir_local!{ idx: Int },
            ],
            self.elem_value_ty.clone(),
            vir::Position::default(),
        )
    }
}


pub struct EncodedSliceTypes<'tcx> {
    pub slice_pred: String,
    pub slice_ty: vir::Type,
    pub elem_ty: vir::Type,
    pub elem_value_ty: vir::Type,
    pub elem_ty_rs: ty::Ty<'tcx>,
    pub lookup_pure_name: String,
    pub slice_len_name: String,
}

impl<'tcx> EncodedSliceTypes<'tcx> {
    pub fn encode_lookup_pure_call(&self, slice: vir::Expr, idx: vir::Expr) -> vir::Expr {
        vir::Expr::func_app(
            self.lookup_pure_name.clone(),
            vec![
                slice,
                idx,
            ],
            vec![
                vir_local!{ self: {self.slice_ty.clone()} },
                vir_local!{ idx: Int },
            ],
            self.elem_value_ty.clone(),
            vir::Position::default(),
        )
    }

    pub fn encode_slice_len_call(&self, slice: vir::Expr) -> vir::Expr {
        vir::Expr::func_app(
            self.slice_len_name.clone(),
            vec![
                slice,
            ],
            vec![
                vir_local!{ self: {self.slice_ty.clone()} },
            ],
            vir::Type::Int,
            vir::Position::default(),
        )
    }
}



pub struct ArrayTypesEncoder {}

impl ArrayTypesEncoder {
    pub fn new() -> Self {
        ArrayTypesEncoder {}
    }

    pub fn encode_slice_types<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        encoder: &'p Encoder<'v, 'tcx>,
        slice_ty: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedSliceTypes<'tcx>> {
        let slice_pred = encoder.encode_type_predicate_use(slice_ty)?;
        let elem_ty_rs = if let ty::TyKind::Slice(elem_ty) = slice_ty.kind() {
            elem_ty
        } else {
            unreachable!()
        };

        let elem_pred = encoder.encode_type_predicate_use(elem_ty_rs)?;

        let slice_ty = encoder.encode_type(slice_ty)?;
        let elem_ty = encoder.encode_type(elem_ty_rs)?;
        let elem_value_ty = encoder.encode_snapshot_type(elem_ty_rs)?;

        // lookup_pure
        let lookup_pure_name = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLookupPure {
                slice_ty_pred: slice_pred.clone(),
                elem_ty_pred: elem_pred.clone(),
                return_ty: elem_value_ty.clone(),
            }
        );

        let slice_len_name = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::SliceLen {
                slice_ty_pred: slice_pred.clone(),
                elem_ty_pred: elem_pred,
            }
        );


        Ok(EncodedSliceTypes{
            slice_pred,
            slice_ty,
            elem_ty,
            elem_value_ty,
            elem_ty_rs,
            lookup_pure_name,
            slice_len_name,
        })
    }

    pub fn encode_array_types<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        encoder: &'p Encoder<'v, 'tcx>,
        array_ty: ty::Ty<'tcx>,
    ) -> EncodingResult<EncodedArrayTypes<'tcx>> {
        // type predicates
        let array_pred = encoder.encode_type_predicate_use(array_ty)?;
        let (elem_ty_rs, len) = if let ty::TyKind::Array(elem_ty, len) = array_ty.kind() {
            (elem_ty, len)
        } else {
            unreachable!()
        };
        let elem_pred = encoder.encode_type_predicate_use(elem_ty_rs)?;

        // types
        let array_ty = encoder.encode_type(array_ty)?;
        let elem_ty = encoder.encode_type(elem_ty_rs)?;
        let elem_value_ty = encoder.encode_snapshot_type(elem_ty_rs)?;

        let array_len = encoder.const_eval_intlike(&len.val)?
            .to_u64().unwrap().try_into().unwrap();

        // lookup_pure
        let lookup_pure_name = encoder.encode_builtin_function_use(
            BuiltinFunctionKind::ArrayLookupPure {
                array_ty_pred: array_pred.clone(),
                elem_ty_pred: elem_pred,
                array_len,
                return_ty: elem_value_ty.clone(),
            }
        );

        Ok(EncodedArrayTypes{
            array_pred,
            array_ty,
            elem_ty,
            elem_value_ty,
            elem_ty_rs,
            array_len,
            lookup_pure_name,
        })
    }
}
