// © 2019-2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


use std::fmt::Display;

use prusti_rustc_interface::middle::ty;
use vir_crate::polymorphic as vir;

use crate::encoder::{
    errors::{EncodingError, EncodingResult},
};


/// Result of encoding a place
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PlaceEncoding<'tcx> {
    /// Just an expression, the most common case.
    Expr(vir::Expr),
    /// Field access expression
    FieldAccess {
        base: Box<PlaceEncoding<'tcx>>,
        field: vir::Field,
    },
    /// Array access expression
    ArrayAccess {
        base: Box<PlaceEncoding<'tcx>>,
        index: vir::Expr,
        encoded_elem_ty: vir::Type,
        rust_array_ty: ty::Ty<'tcx>,
    },
    /// Variant (i.e. enum access)
    Variant {
        base: Box<PlaceEncoding<'tcx>>,
        field: vir::Field,
    },
    /// Slice indexing projection
    SliceAccess {
        base: Box<PlaceEncoding<'tcx>>,
        index: vir::Expr,
        encoded_elem_ty: vir::Type,
        rust_slice_ty: ty::Ty<'tcx>,
    },
}

/// Return type of PlaceEncoding::into_array_base
pub enum ExprOrArrayBase {
    Expr(vir::Expr),
    ArrayBase(vir::Expr),
    #[allow(dead_code)]
    SliceBase(vir::Expr),
}

impl<'tcx> PlaceEncoding<'tcx> {
    pub fn try_into_expr(self) -> EncodingResult<vir::Expr> {
        match self.into_array_base() {
           ExprOrArrayBase::Expr(e) => Ok(e),
           ExprOrArrayBase::ArrayBase(b)
           | ExprOrArrayBase::SliceBase(b) => Err(EncodingError::internal(
               format!("PlaceEncoding::try_into_expr called on sequence expr '{b:?}'")
           )),
        }
    }

    /// Returns the base variable of an array access, if any of the nested places are an array
    /// access, else just the same expr that `try_into_expr` would
    pub fn into_array_base(self) -> ExprOrArrayBase {
        match self {
            PlaceEncoding::Expr(e) => ExprOrArrayBase::Expr(e),
            PlaceEncoding::FieldAccess { base, field } => {
                match base.into_array_base() {
                    ExprOrArrayBase::Expr(e) => ExprOrArrayBase::Expr(e.field(field)),
                    base@ExprOrArrayBase::ArrayBase(_) => base,
                    base@ExprOrArrayBase::SliceBase(_) => base,
                }
            }
            PlaceEncoding::Variant { base, field } => {
                match base.into_array_base() {
                    ExprOrArrayBase::Expr(e) => ExprOrArrayBase::Expr(
                        vir::Expr::Variant( vir::Variant {base: Box::new(e), variant_index: field, position: vir::Position::default()} )
                    ),
                    base@ExprOrArrayBase::ArrayBase(_) => base,
                    base@ExprOrArrayBase::SliceBase(_) => base,
                }
            }
            PlaceEncoding::ArrayAccess { base, .. } => {
                // need to check base's into_expr_or_array_base, maybe we're not the outermost
                // array
                match base.into_array_base() {
                    ExprOrArrayBase::Expr(e) => ExprOrArrayBase::ArrayBase(e),
                    base@ExprOrArrayBase::ArrayBase(_) => base,
                    base@ExprOrArrayBase::SliceBase(_) => base,
                }
            }
            PlaceEncoding::SliceAccess { base, .. } => {
                match base.into_array_base() {
                    ExprOrArrayBase::Expr(e) => ExprOrArrayBase::SliceBase(e),
                    base@ExprOrArrayBase::ArrayBase(_) => base,
                    base@ExprOrArrayBase::SliceBase(_) => base,
                }
            }
        }
    }

    pub fn field(self, field: vir::Field) -> Self {
        PlaceEncoding::FieldAccess { base: Box::new(self), field }
    }

    pub fn get_type(&self) -> &vir::Type {
        match self {
            PlaceEncoding::Expr(ref e) => e.get_type(),
            PlaceEncoding::FieldAccess { ref field, .. } => &field.typ,
            PlaceEncoding::ArrayAccess { ref encoded_elem_ty, .. } => encoded_elem_ty,
            PlaceEncoding::Variant { ref field, .. } => &field.typ,
            PlaceEncoding::SliceAccess { ref encoded_elem_ty, .. } => encoded_elem_ty,
        }
    }

    pub fn variant(self, index: &str) -> Self {
        // TODO: somewhat duplicate from vir::Expr::variant()
        let field_name = format!("enum_{index}");
        let field = vir::Field::new(field_name, self.get_type().clone().variant(index));

        PlaceEncoding::Variant { base: Box::new(self), field }
    }
}

impl<'tcx> From<vir::Expr> for PlaceEncoding<'tcx> {
    fn from(e: vir::Expr) -> Self {
        PlaceEncoding::Expr(e)
    }
}

impl<'tcx> Display for PlaceEncoding<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceEncoding::Expr(e) => write!(f, "{e}"),
            PlaceEncoding::FieldAccess { base, field } => write!(f, "{base}.{field}"),
            PlaceEncoding::ArrayAccess { base, index, .. } => write!(f, "{base}[{index}]"),
            PlaceEncoding::Variant { base, field } => write!(f, "{base}[{field}]"),
            PlaceEncoding::SliceAccess { base, index, .. } => write!(f, "{base}[{index}]"),
        }
    }
}
