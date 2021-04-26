// © 2019-2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


use std::fmt::Display;

use prusti_common::vir;

use crate::encoder::{
    Encoder,
    errors::{EncodingError, EncodingResult},
};


/// Result of encoding a place
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PlaceEncoding {
    /// Just an expression, the most common case.
    Expr(vir::Expr),
    /// Field access expression
    FieldAccess {
        base: Box<PlaceEncoding>,
        field: vir::Field,
    },
    /// Array access expression
    ArrayAccess {
        base: Box<PlaceEncoding>,
        index: vir::Expr,
        array_elem_ty: vir::Type,
        array_len: usize,
        lookup_pure_ret: vir::Type,
        val_field: vir::Field,
    },
    Variant {
        base: Box<PlaceEncoding>,
        field: vir::Field,
    }
}

impl PlaceEncoding {
    pub fn try_into_expr(self) -> EncodingResult<vir::Expr> {
        match self {
            PlaceEncoding::Expr(e) => Ok(e),
            PlaceEncoding::FieldAccess { base, field } => {
                Ok(base.try_into_expr()?.field(field))
            },
            PlaceEncoding::Variant { base, field } => {
                Ok(vir::Expr::Variant(box base.try_into_expr()?, field, vir::Position::default()))
            },
            other => Err(EncodingError::internal(format!("PlaceEncoding::try_into_expr called on non-expr '{:?}'", other))),
        }
    }

    pub fn field(self, field: vir::Field) -> Self {
        PlaceEncoding::FieldAccess { base: box self, field }
    }

    pub fn get_type(&self) -> &vir::Type {
        match self {
            PlaceEncoding::Expr(ref e) => e.get_type(),
            PlaceEncoding::FieldAccess { ref field, .. } => &field.typ,
            PlaceEncoding::ArrayAccess { ref array_elem_ty, .. } => array_elem_ty,
            PlaceEncoding::Variant { ref field, .. } => &field.typ,
        }
    }

    pub fn variant(self, index: &str) -> Self {
        // TODO: somewhat duplicate from vir::Expr::variant()
        let field_name = format!("enum_{}", index);
        let field = vir::Field::new(field_name, self.get_type().clone().variant(index));

        PlaceEncoding::Variant { base: box self, field }
    }
}

impl From<vir::Expr> for PlaceEncoding {
    fn from(e: vir::Expr) -> Self {
        PlaceEncoding::Expr(e)
    }
}

impl Display for PlaceEncoding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceEncoding::Expr(e) => write!(f, "{}", e),
            PlaceEncoding::FieldAccess { base, field } => write!(f, "{}.{}", base, field),
            PlaceEncoding::ArrayAccess { base, index, .. } => write!(f, "{}[{}]", base, index),
            PlaceEncoding::Variant { base, field } => write!(f, "{}[{}]", base, field),
        }
    }
}
