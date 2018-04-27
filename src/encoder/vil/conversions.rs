// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vil::ast::*;

impl From<LocalVar> for Place {
    fn from(local_var: LocalVar) -> Self {
        Place::Base(local_var)
    }
}

impl From<LocalVar> for Expr {
    fn from(local_var: LocalVar) -> Self {
        Expr::Place(local_var.into())
    }
}

impl From<Place> for Expr {
    fn from(place: Place) -> Self {
        Expr::Place(place)
    }
}

impl From<Const> for Expr {
    fn from(cons: Const) -> Self {
        Expr::Const(cons)
    }
}

impl From<bool> for Const {
    fn from(val: bool) -> Self {
        Const::Bool(val)
    }
}

impl From<bool> for Expr {
    fn from(val: bool) -> Self {
        Expr::Const(val.into())
    }
}

impl From<i32> for Const {
    fn from(val: i32) -> Self {
        Const::Int(val as i64)
    }
}

impl From<u32> for Expr {
    fn from(val: u32) -> Self {
        Expr::Const(val.into())
    }
}

impl From<u32> for Const {
    fn from(val: u32) -> Self {
        Const::Int(val as i64)
    }
}

impl From<i32> for Expr {
    fn from(val: i32) -> Self {
        Expr::Const(val.into())
    }
}

impl From<i64> for Const {
    fn from(val: i64) -> Self {
        Const::Int(val)
    }
}

impl From<i64> for Expr {
    fn from(val: i64) -> Self {
        Expr::Const(val.into())
    }
}

impl From<u64> for Const {
    fn from(val: u64) -> Self {
        Const::BigInt(format!("{}", val))
    }
}

impl From<u64> for Expr {
    fn from(val: u64) -> Self {
        Expr::Const(val.into())
    }
}

impl From<u128> for Const {
    fn from(val: u128) -> Self {
        Const::BigInt(format!("{}", val))
    }
}

impl From<u128> for Expr {
    fn from(val: u128) -> Self {
        Expr::Const(val.into())
    }
}

impl From<usize> for Const {
    fn from(val: usize) -> Self {
        Const::BigInt(format!("{}", val))
    }
}

impl From<usize> for Expr {
    fn from(val: usize) -> Self {
        Expr::Const(val.into())
    }
}
