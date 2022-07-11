// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::ty;


pub mod to_string;
pub mod type_visitor;

pub fn ty_to_string(typ: &ty::TyKind) -> String {
    (match typ {
        &ty::TyKind::Bool => "bool type",
        &ty::TyKind::Char => "char type",
        &ty::TyKind::Int(_) => "int type",
        &ty::TyKind::Uint(_) => "uint type",
        &ty::TyKind::Float(_) => "float type",
        &ty::TyKind::Adt(_, _) => "algebraic data type",
        &ty::TyKind::Foreign(_) => "foreign function interface",
        &ty::TyKind::Str => "string",
        &ty::TyKind::Array(..) => "array",
        &ty::TyKind::Slice(_) => "array slice",
        &ty::TyKind::RawPtr(_) => "raw pointer",
        &ty::TyKind::Ref(..) => "reference",
        &ty::TyKind::FnDef(_, _) => "function defintion",
        &ty::TyKind::FnPtr(_) => "function pointer",
        &ty::TyKind::Dynamic(..) => "trait object",
        &ty::TyKind::Closure(_, _) => "closures",
        &ty::TyKind::Generator(..) | &ty::TyKind::GeneratorWitness(..) => "generator",
        &ty::TyKind::Never => "never type",
        &ty::TyKind::Tuple(_) => "tuple",
        &ty::TyKind::Projection(_) => "projection",
        &ty::TyKind::Opaque(_, _) => "opaque type",
        &ty::TyKind::Param(_) => "type parameter",
        &ty::TyKind::Bound(_, _) => "bound type variable",
        &ty::TyKind::Placeholder(_) => "placeholder type",
        &ty::TyKind::Infer(_) => "inference type",
        &ty::TyKind::Error(_) => "error type",
    }).to_string()
}

pub fn is_reference(base_ty: ty::Ty) -> bool {
    matches!(base_ty.kind(), ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..))
}