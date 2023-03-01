// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    index::vec::{Idx, IndexVec},
    middle::mir::Operand,
};
use std::fmt::{Debug, Formatter};

#[derive(Clone, Debug, Deref, DerefMut)]
pub struct Operands<'tcx> {
    operands: IndexVec<Temporary, Operand<'tcx>>,
}
impl<'tcx> Operands<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            operands: IndexVec::new(),
        }
    }
    pub(crate) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> MicroOperand {
        let index = self.operands.push(operand.clone());
        MicroOperand::new(index)
    }
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Deref, DerefMut)]
pub struct MicroOperand(Temporary);
impl MicroOperand {
    pub const fn new(value: Temporary) -> Self {
        Self(value)
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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "tmp{}", self.private)
    }
}
