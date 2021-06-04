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
};
use prusti_common::{
    vir,
    vir_local,
};


pub struct EncodedArrayTypes<'tcx> {
    pub array_pred: String,
    pub array_ty: vir::Type,
    pub elem_pred: String,
    pub elem_ty: vir::Type,
    pub elem_value_ty: vir::Type,
    pub elem_ty_rs: ty::Ty<'tcx>,
    pub array_len: usize,
}

pub struct EncodedSliceTypes<'tcx> {
    pub slice_pred: String,
    pub slice_ty: vir::Type,
    pub elem_pred: String,
    pub elem_ty: vir::Type,
    pub elem_value_ty: vir::Type,
    pub elem_ty_rs: ty::Ty<'tcx>,
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

        Ok(EncodedSliceTypes{
            slice_pred,
            slice_ty,
            elem_pred,
            elem_ty,
            elem_value_ty,
            elem_ty_rs,
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

        Ok(EncodedArrayTypes{
            array_pred,
            array_ty,
            elem_pred,
            elem_ty,
            elem_value_ty,
            elem_ty_rs,
            array_len,
        })
    }
}
