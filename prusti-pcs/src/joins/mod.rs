// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]

mod packup;
mod repackjoin;
mod repackweaken;
mod unify;

pub use packup::*;
pub use repackjoin::*;
pub use repackweaken::*;
pub use unify::*;

use crate::syntax::{MicroMirStatement, PCSPermission};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{
            AggregateKind::*, Body, Local, Mutability, Operand, Operand::*, Place, Rvalue::*,
            StatementKind::*, Terminator, TerminatorKind, TerminatorKind::*,
        },
        ty::TyCtxt,
    },
};

/// Represents any transformation of the free PCS we are permitted to do
pub trait Repacking<'tcx> {
    /// Transform the repacking into a sequence of MicroMir statements
    fn encode(&self) -> Vec<MicroMirStatement<'tcx>>;
}

#[derive(Clone, Debug)]
pub struct PermissionSet<'tcx>(pub FxHashSet<PCSPermission<'tcx>>);

impl<'tcx> Default for PermissionSet<'tcx> {
    fn default() -> Self {
        PermissionSet {
            0: FxHashSet::default(),
        }
    }
}

impl<'tcx> PermissionSet<'tcx> {
    pub fn from_vec(vec: Vec<PCSPermission<'tcx>>) -> Self {
        PermissionSet {
            0: vec.iter().cloned().collect(),
        }
    }
}

fn usize_place<'tcx>(id: usize) -> mir::Place<'tcx> {
    mir::Local::from_usize(id).into()
}
