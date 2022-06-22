// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
#![allow(unused_imports)]

use crate::syntactic_expansion;
use rustc_data_structures::{stable_map::FxHashMap, stable_set::FxHashSet};
use rustc_index::vec::IndexVec;
use rustc_middle::mir::{
    terminator::SwitchTargets, BasicBlock, BinOp, Constant, Local, Location, Mutability,
    Mutability::*, NullOp, Place, PlaceElem, Statement, UnOp,
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

    pub fn empty() -> Self {
        PCS {
            set: FxHashSet::default(),
        }
    }
}

pub struct MicroMirData<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub terminator: MicroMirTerminator<'tcx>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct TemporaryPlace {
    pub id: usize,
}

/// Unlike the real MIR, we will not represent conditional flags as stack places.
/// This makes the implementation simpler, gives us more freedom for the backend
/// encoding, and we're modelleing drops ourselves anyways.
///
/// TODO: Encode this and analyze it
#[derive(PartialEq, Eq, Hash, Clone)]
pub struct ConditionalFlag {
    id: usize,
    kind: ConditionalFlagKind,
}

// Approximations we need to compute the MicroMir (Permissions, approximate)
//
//      DefinitelyInitialized
//
//
// Annotations we need to compute the MicroMir (Non-permission factors, non-approximate)
//
//      Flags for real initilizations / Reassignments (tags)
//
//      Real lifetime endings
//
//

// Control flow === lifetime flow dependendent ops

// Special edge === wand \
// fields of owned,
// field of a borrowed place,
// regular borrows
//      ==> derivable from type info @ asssignments with RHS borrow

// move/copy might have DAG effect, undecided if uninit is meaningful to DAG
// Tag at every reassignment, not just at loop
//      => know statically reassignment places, syntactic rule.

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum ConditionalFlagKind {
    Init,
}

pub enum MicroMirStatement<'tcx> {
    Nop,
    Set(TemporaryPlace, Place<'tcx>, Mutability),
    Move(Place<'tcx>, TemporaryPlace),
    Duplicate(Place<'tcx>, TemporaryPlace, Mutability),
    Constant(Constant<'tcx>, TemporaryPlace),
    Kill(LinearResource<'tcx>),
    NullOp(NullOp, TemporaryPlace),
    UnOp(UnOp, TemporaryPlace, TemporaryPlace),
    BinaryOp(BinOp, bool, TemporaryPlace, TemporaryPlace, TemporaryPlace),
    Len(Place<'tcx>, TemporaryPlace, Mutability),
}

pub enum MicroMirTerminator<'tcx> {
    Jump(BasicBlock),
    JumpInt(LinearResource<'tcx>, Vec<(u128, BasicBlock)>, Mutability),
    Return(Mutability),
    EndVerif,
}

trait HoareSemantics {
    type PRE;
    type POST;
    fn precondition(&self) -> Option<Self::PRE>;
    fn postcondition(&self) -> Option<Self::POST>;
}

impl<'tcx> HoareSemantics for MicroMirStatement<'tcx> {
    type PRE = PCS<'tcx>;

    fn precondition(&self) -> Option<Self::PRE> {
        match self {
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
            MicroMirStatement::Constant(_, _) => Some(PCS::empty()),
            MicroMirStatement::Kill(_) => None,
            MicroMirStatement::NullOp(_, _) => Some(PCS::empty()),
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

    type POST = PCS<'tcx>;

    fn postcondition(&self) -> Option<Self::POST> {
        match self {
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
            MicroMirStatement::Constant(_, t) => {
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

impl<'tcx> HoareSemantics for MicroMirTerminator<'tcx> {
    type PRE = PCS<'tcx>;

    fn precondition(&self) -> Option<Self::PRE> {
        match self {
            MicroMirTerminator::Jump(_) => Some(PCS::empty()),
            MicroMirTerminator::JumpInt(t, _, m) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    *m,
                    (*t).into(),
                )]))
            }
            MicroMirTerminator::Return(m) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    *m,
                    LinearResource::new_from_local_id(0),
                )]))
            }
            MicroMirTerminator::EndVerif => None,
        }
    }

    type POST = Vec<(BasicBlock, PCS<'tcx>)>;

    fn postcondition(&self) -> Option<Self::POST> {
        match self {
            MicroMirTerminator::Jump(bb) => Some(vec![(*bb, PCS::empty())]),
            MicroMirTerminator::JumpInt(t, mir_targets, m) => {
                let target_permissions: Vec<(BasicBlock, PCS<'tcx>)> = mir_targets
                    .iter()
                    .map(|(_, bb)| {
                        (
                            *bb,
                            PCS::from_vec(vec![PCSPermission::new_initialized(*m, *t)]),
                        )
                    })
                    .collect();
                Some(target_permissions)
            }
            MicroMirTerminator::Return(_) => None,
            MicroMirTerminator::EndVerif => None,
        }
    }
}

impl<'tcx> MicroMirBody<'tcx> {
    pub fn statement_at(&self, location: Location) -> &MicroMirStatement {
        return &self.body[location.block].statements[location.statement_index];
    }

    pub fn terminator_of(&self, location: Location) -> &MicroMirTerminator {
        return &self.body[location.block].terminator;
    }

    pub fn terminator_of_bb(&self, bb: BasicBlock) -> &MicroMirTerminator {
        return &self.body[bb].terminator;
    }

    /// Read off the precondition for the core memory safety proof
    /// INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    /// INVARIANT: The final MicroMir has no preconditions that are NONE
    pub fn core_precondition(&self, location: Location) -> Option<PCS> {
        self.statement_at(location).precondition()
    }

    /// Read off the precondition for the core memory safety proof
    /// INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    /// INVARIANT: The final MicroMir has no postconditions that are NONE
    pub fn core_postcondition(&self, location: Location) -> Option<PCS> {
        self.statement_at(location).postcondition()
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

impl<'tcx> LinearResource<'tcx> {
    pub fn new_from_local_id(id: usize) -> Self {
        LinearResource::Mir(Local::from_usize(id).into())
    }
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
