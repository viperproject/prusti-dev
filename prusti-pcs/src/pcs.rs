// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
#![allow(unused_imports)]
use rustc_data_structures::{stable_map::FxHashMap, stable_set::FxHashSet};
use rustc_index::vec::IndexVec;
use rustc_middle::mir::{
    BasicBlock, BinOp, Constant, Local, Location, NullOp, Place, PlaceElem, UnOp,
};
pub struct MicroMirBody<'tcx> {
    pub body: IndexVec<BasicBlock, MicroMirData<'tcx>>,
    pub kill_elaborations: FxHashMap<Location, PCS<'tcx>>,
    pub required_prestates: FxHashMap<Location, PCS<'tcx>>,
}

pub struct PCS<'tcx> {
    set: FxHashSet<PCSPermission<'tcx>>,
}

impl<'tcx> PCS<'tcx> {
    pub fn from_vec(vec: Vec<PCSPermission<'tcx>>) -> Self {
        PCS {
            set: FxHashSet::from_iter(vec),
        }
    }
}

pub struct MicroMirData<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub terminator: MicroMirTerminator,
}

pub struct MicroMirTerminator {
    kind: MicroMirTerminatorKind,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct TemporaryPlace {
    id: usize,
}

pub enum MicroMirStatement<'tcx> {
    Nop,
    Set(TemporaryPlace, Place<'tcx>, Mutability),
    Move(Place<'tcx>, TemporaryPlace),
    Duplicate(Place<'tcx>, TemporaryPlace, Mutability),
    Constant(TemporaryPlace, Constant<'tcx>),
    Kill(LinearResource<'tcx>),
    NullOp(NullOp, TemporaryPlace),
    UnOp(UnOp, TemporaryPlace, TemporaryPlace),
    BinaryOp(BinOp, bool, TemporaryPlace, TemporaryPlace, TemporaryPlace),
    Len(Place<'tcx>, TemporaryPlace, Mutability),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Mutability {
    Mut,
    Not,
}
pub enum MicroMirTerminatorKind {
    // WIP
    Goto,
    // ...
}

impl MicroMirTerminatorKind {
    // WIP
    pub fn core_precondition(&self) {
        todo!();
    }
}

impl<'tcx> MicroMirBody<'tcx> {
    pub fn statement_at(&self, location: Location) -> &MicroMirStatement {
        return &self.body[location.block].statements[location.statement_index];
    }

    /// Read off the precondition for the core memory safety proof
    /// INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    /// INVARIANT: The final MicroMir has no preconditions that are NONE
    pub fn core_precondition(&self, location: Location) -> Option<PCS> {
        match self.statement_at(location) {
            MicroMirStatement::Nop => Some(PCS::from_vec(vec![])),
            MicroMirStatement::Set(t, p, m) => Some(PCS::from_vec(vec![
                PCSPermission::new_initialized(*m, (*t).into()),
                PCSPermission::new_uninit((*p).into()),
            ])),
            MicroMirStatement::Move(p, _) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*p).into(),
                )]))
            }
            MicroMirStatement::Duplicate(p, _, m) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    *m,
                    (*p).into(),
                )]))
            }
            MicroMirStatement::Constant(_, _) => Some(PCS::from_vec(vec![])),
            MicroMirStatement::Kill(_) => None,
            MicroMirStatement::NullOp(_, _) => Some(PCS::from_vec(vec![])),
            MicroMirStatement::UnOp(_, t1, _) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*t1).into(),
                )]))
            }
            MicroMirStatement::BinaryOp(_, _, t1, t2, _) => Some(PCS::from_vec(vec![
                PCSPermission::new_initialized(Mutability::Mut, (*t1).into()),
                PCSPermission::new_initialized(Mutability::Mut, (*t2).into()),
            ])),
            MicroMirStatement::Len(p, _, m) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    *m,
                    (*p).into(),
                )]))
            }
        }
    }

    /// Read off the precondition for the core memory safety proof
    /// INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    /// INVARIANT: The final MicroMir has no postconditions that are NONE
    pub fn core_postcondition(&self, location: Location) -> Option<PCS> {
        match self.statement_at(location) {
            MicroMirStatement::Nop => Some(PCS::from_vec(vec![])),
            MicroMirStatement::Set(_, p, m) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    *m,
                    (*p).into(),
                )]))
            }
            MicroMirStatement::Move(p, t) => Some(PCS::from_vec(vec![
                PCSPermission::new_uninit((*p).into()),
                PCSPermission::new_initialized(Mutability::Mut, (*t).into()),
            ])),
            MicroMirStatement::Duplicate(p, t, m) => Some(PCS::from_vec(vec![
                PCSPermission::new_initialized(*m, (*p).into()),
                PCSPermission::new_initialized(Mutability::Mut, (*t).into()),
            ])),
            MicroMirStatement::Constant(t, _) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*t).into(),
                )]))
            }
            MicroMirStatement::Kill(p) => Some(PCS::from_vec(vec![PCSPermission::new_uninit(*p)])),
            MicroMirStatement::NullOp(_, t1) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*t1).into(),
                )]))
            }
            MicroMirStatement::UnOp(_, _, t2) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*t2).into(),
                )]))
            }
            MicroMirStatement::BinaryOp(_, _, _, _, t3) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*t3).into(),
                )]))
            }
            MicroMirStatement::Len(p, t, m) => Some(PCS::from_vec(vec![
                PCSPermission::new_initialized(*m, (*p).into()),
                PCSPermission::new_initialized(Mutability::Mut, (*t).into()),
            ])),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PCSPermissionKind {
    Shared,
    Exclusive,
    Uninit,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum LinearResource<'tcx> {
    Mir(Place<'tcx>),
    Tmp(TemporaryPlace),
}

impl<'tcx> From<Place<'tcx>> for LinearResource<'tcx> {
    fn from(p: Place<'tcx>) -> Self {
        LinearResource::Mir(p)
    }
}

impl<'tcx> From<TemporaryPlace> for LinearResource<'tcx> {
    fn from(t: TemporaryPlace) -> Self {
        LinearResource::Tmp(t)
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PCSPermission<'tcx> {
    target: LinearResource<'tcx>,
    kind: PCSPermissionKind,
}

impl<'tcx> PCSPermission<'tcx> {
    pub fn new_initialized(m: Mutability, target: LinearResource<'tcx>) -> Self {
        match m {
            Mutability::Mut => PCSPermission {
                target,
                kind: PCSPermissionKind::Exclusive,
            },
            Mutability::Not => PCSPermission {
                target,
                kind: PCSPermissionKind::Shared,
            },
        }
    }

    pub fn new_uninit(target: LinearResource<'tcx>) -> Self {
        PCSPermission {
            target,
            kind: PCSPermissionKind::Uninit,
        }
    }
}

pub fn init_analysis() {}

// TODO ITEMS:
//   Prefix invariant in init semantics
//   Operational translation
//   Calling the conditional analysis (refactored for operational MIR)
//   Kill elaboration into MicroMir
