// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    index::vec::{Idx, IndexVec},
    middle::mir::{Constant, Operand},
};
use std::fmt::{Debug, Formatter, Result};

use crate::Place;

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MicroFullOperand<'tcx> {
    Copy(Place<'tcx>),
    Move(Place<'tcx>),
    Constant(Box<Constant<'tcx>>),
}

impl<'tcx> From<&Operand<'tcx>> for MicroFullOperand<'tcx> {
    fn from(value: &Operand<'tcx>) -> Self {
        match value {
            &Operand::Copy(p) => MicroFullOperand::Copy(p.into()),
            &Operand::Move(p) => MicroFullOperand::Move(p.into()),
            Operand::Constant(c) => MicroFullOperand::Constant(c.clone()),
        }
    }
}

/// Note that one can have the same `Local` multiple times in the `Operands` vector
/// for a single statement. For example in the following code:
/// ```
/// struct S { a: bool, b: bool, c: bool }
/// fn true_a(s: &S) -> S {
///     S { a: true, .. *s }
/// }
/// ```
#[derive(Clone, Debug, Deref, DerefMut)]
pub struct Operands<'tcx>(IndexVec<Temporary, MicroFullOperand<'tcx>>);
impl<'tcx> Operands<'tcx> {
    pub(crate) fn new() -> Self {
        Self(IndexVec::new())
    }
    pub(crate) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> MicroOperand {
        let index = self.push(operand.into());
        MicroOperand::new(index)
    }
}

#[derive(Clone, Copy, Hash, Eq, PartialEq, Deref, DerefMut)]
pub struct MicroOperand(Temporary);
impl MicroOperand {
    pub const fn new(value: Temporary) -> Self {
        Self(value)
    }
}
impl Debug for MicroOperand {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}", self.0)
    }
}

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct Temporary {
    private: u32,
}
impl Temporary {
    pub const fn from_usize(value: usize) -> Self {
        Self {
            private: value as u32,
        }
    }
    pub const fn from_u32(value: u32) -> Self {
        Self { private: value }
    }
    pub const fn as_u32(self) -> u32 {
        self.private
    }
    pub const fn as_usize(self) -> usize {
        self.private as usize
    }
}
impl Idx for Temporary {
    fn new(value: usize) -> Self {
        Self {
            private: value as u32,
        }
    }
    fn index(self) -> usize {
        self.private as usize
    }
}
impl Debug for Temporary {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "tmp{}", self.private)
    }
}
