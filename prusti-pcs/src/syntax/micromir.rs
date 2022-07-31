// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
#![allow(unused_imports)]

use crate::{syntax, syntax::hoare_semantics::*, util::*};
use analysis::mir_utils::expand_struct_place;
use env_logger::Env;
use itertools::Itertools;
use prusti_interface::{
    environment::{mir_storage, Environment},
    specs,
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::{stable_map::FxHashMap, stable_set::FxHashSet},
    errors::MultiSpan,
    index::vec::IndexVec,
    middle::{
        mir::{
            self, AggregateKind, BasicBlock, BinOp, Body, Constant, Local, LocalDecl, Location,
            Mutability, Mutability::*, NullOp, Place, PlaceElem, ProjectionElem::Field, Rvalue,
            Statement, SwitchTargets, UnOp,
        },
        ty::{self, AdtKind, Ty, TyCtxt, TyKind},
    },
};
use std::{
    cmp::Ordering,
    fmt::{Debug, Display},
    iter::FromIterator,
};

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct TemporaryPlace {
    pub id: usize,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum LinearResource<'tcx> {
    Mir(Place<'tcx>),
    Tmp(TemporaryPlace),
}

#[derive(Clone)]
pub enum MicroMirStatement<'tcx> {
    Nop,
    Set(TemporaryPlace, Place<'tcx>, Mutability),
    Move(Place<'tcx>, TemporaryPlace),
    Duplicate(Place<'tcx>, TemporaryPlace, Mutability),
    Constant(Constant<'tcx>, TemporaryPlace),
    // Precondition is allowed to be None
    Kill(Option<Vec<PCSPermission<'tcx>>>, LinearResource<'tcx>),
    NullOp(NullOp, TemporaryPlace),
    UnOp(UnOp, TemporaryPlace, TemporaryPlace),
    BinaryOp(BinOp, bool, TemporaryPlace, TemporaryPlace, TemporaryPlace),
    Len(Place<'tcx>, TemporaryPlace, Mutability),
    // Aggregate probably needs more information
    Aggregate(Place<'tcx>, Vec<PCSPermission<'tcx>>, Mutability),
    // These two are probably useless
    Allocate(Place<'tcx>),
    Deallocate(Place<'tcx>),
    // Places annotated so that we do not need to truck around the mir
    Pack(Vec<Place<'tcx>>, Place<'tcx>),
    Unpack(Place<'tcx>, Vec<Place<'tcx>>),
}

#[derive(Clone)]
pub enum MicroMirTerminator<'tcx> {
    Jump(BasicBlock),
    JumpInt(LinearResource<'tcx>, Vec<(u128, BasicBlock)>, Mutability),
    Return(Mutability),
    FailVerif,
}

pub struct MicroMirData<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub terminator: MicroMirTerminator<'tcx>,
    pub mir_parent: Vec<usize>,
    pub mir_block: BasicBlock,
}

pub struct MicroMirBody<'tcx> {
    pub body: IndexVec<BasicBlock, MicroMirData<'tcx>>,
    pub kill_elaborations: FxHashMap<Location, PCS<'tcx>>,
    pub required_prestates: FxHashMap<Location, PCS<'tcx>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Ord, PartialOrd)]
pub enum PCSPermissionKind {
    Shared,
    Exclusive,
    Uninit,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PCSPermission<'tcx> {
    pub target: LinearResource<'tcx>,
    pub kind: PCSPermissionKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PCS<'tcx> {
    pub set: FxHashSet<PCSPermission<'tcx>>,
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

    pub fn pprint_contents(&self) {
        for s in self.set.iter() {
            print!("{:#?}, ", s)
        }
    }
}

impl<'tcx> HoareSemantics for MicroMirStatement<'tcx> {
    type PRE = Option<PCS<'tcx>>;

    fn precondition(&self) -> Self::PRE {
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
            MicroMirStatement::Kill(pre, _) => {
                pre.clone().and_then(|pre_v| Some(PCS::from_vec(pre_v)))
            }
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
            MicroMirStatement::Allocate(_) => Some(PCS::empty()),
            MicroMirStatement::Deallocate(p) => {
                Some(PCS::from_vec(vec![PCSPermission::new_uninit((*p).into())]))
            }
            // Assumption: All places are mutably owned
            MicroMirStatement::Pack(ps, _) => Some(PCS::from_vec(
                ps.into_iter()
                    .map(|p| PCSPermission::new_initialized(Mutability::Mut, (*p).into()))
                    .collect(),
            )),
            MicroMirStatement::Unpack(p, _) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*p).into(),
                )]))
            }
            MicroMirStatement::Aggregate(dest, subpermissions, _) => {
                let mut pcs = PCS::from_vec(subpermissions.to_vec());
                pcs.set.insert(PCSPermission::new_uninit((*dest).into()));
                Some(pcs)
            }
        }
    }

    type POST = Option<PCS<'tcx>>;

    fn postcondition(&self) -> Self::POST {
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
            MicroMirStatement::Kill(_, p) => {
                Some(PCS::from_vec(vec![PCSPermission::new_uninit(*p)]))
            }
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
            MicroMirStatement::Deallocate(_) => Some(PCS::empty()),
            MicroMirStatement::Allocate(p) => {
                Some(PCS::from_vec(vec![PCSPermission::new_uninit((*p).into())]))
            }
            // Assumption: All places are mutably owned
            MicroMirStatement::Unpack(_, ps) => Some(PCS::from_vec(
                ps.into_iter()
                    .map(|p| PCSPermission::new_initialized(Mutability::Mut, (*p).into()))
                    .collect(),
            )),
            MicroMirStatement::Pack(_, p) => {
                Some(PCS::from_vec(vec![PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*p).into(),
                )]))
            }
            MicroMirStatement::Aggregate(p, subpermissions, m) => {
                let mut pcs = PCS::from_vec(vec![PCSPermission::new_initialized(*m, (*p).into())]);
                for permission in subpermissions.iter() {
                    if let r @ LinearResource::Mir(_) = permission.target {
                        pcs.set.insert(PCSPermission::new_uninit(r));
                    }
                }
                Some(pcs)
            }
        }
    }
}

impl<'tcx> HoareSemantics for MicroMirTerminator<'tcx> {
    type PRE = PCS<'tcx>;

    fn precondition(&self) -> Self::PRE {
        match self {
            MicroMirTerminator::Jump(_) => PCS::empty(),
            MicroMirTerminator::JumpInt(t, _, m) => {
                PCS::from_vec(vec![PCSPermission::new_initialized(*m, (*t).into())])
            }
            MicroMirTerminator::Return(m) => PCS::from_vec(vec![PCSPermission::new_initialized(
                *m,
                LinearResource::new_from_local_id(0),
            )]),
            MicroMirTerminator::FailVerif => PCS::empty(),
        }
    }

    type POST = Vec<(BasicBlock, PCS<'tcx>)>;

    fn postcondition(&self) -> Self::POST {
        match self {
            MicroMirTerminator::Jump(bb) => vec![(*bb, PCS::empty())],
            MicroMirTerminator::JumpInt(t, mir_targets, m) => mir_targets
                .iter()
                .map(|(_, bb)| {
                    (
                        *bb,
                        PCS::from_vec(vec![PCSPermission::new_initialized(*m, *t)]),
                    )
                })
                .collect(),
            MicroMirTerminator::Return(_) => vec![],
            MicroMirTerminator::FailVerif => vec![],
        }
    }
}

impl<'tcx> MicroMirBody<'tcx> {
    pub fn statement_at(&self, location: Location) -> &'tcx MicroMirStatement {
        return &self.body[location.block].statements[location.statement_index];
    }

    pub fn terminator_of(&self, location: Location) -> &'tcx MicroMirTerminator {
        return &self.body[location.block].terminator;
    }

    pub fn terminator_of_bb(&self, bb: BasicBlock) -> &'tcx MicroMirTerminator {
        return &self.body[bb].terminator;
    }

    // Read off the precondition for the core memory safety proof
    // INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    // INVARIANT: The final MicroMir has no preconditions that are NONE
    pub fn core_precondition(&'tcx self, location: Location) -> Option<PCS<'tcx>> {
        self.statement_at(location).precondition()
    }

    // Read off the precondition for the core memory safety proof
    // INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    // INVARIANT: The final MicroMir has no postconditions that are NONE
    pub fn core_postcondition(&'tcx self, location: Location) -> Option<PCS<'tcx>> {
        self.statement_at(location).postcondition()
    }
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

    pub fn retrieve_place(&self) -> EncodingResult<Place<'tcx>> {
        match self.target {
            LinearResource::Mir(pl) => Ok(pl),
            LinearResource::Tmp(_) => Err(PrustiError::internal(
                "can not retrive underlying place from temporary resource",
                MultiSpan::new(),
            )),
        }
    }
}

impl Debug for TemporaryPlace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_tmp{}", self.id)
    }
}

impl<'tcx> Debug for LinearResource<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Mir(p) => write!(f, "{:?}", p),
            Self::Tmp(t) => write!(f, "{:?}", t),
        }
    }
}

impl Debug for PCSPermissionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCSPermissionKind::Shared => write!(f, "s"),
            PCSPermissionKind::Exclusive => write!(f, "e"),
            PCSPermissionKind::Uninit => write!(f, "u"),
        }
    }
}

impl<'tcx> Debug for PCSPermission<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} {:?}", self.kind, self.target)
    }
}

impl<'tcx> Debug for MicroMirStatement<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MicroMirStatement::Nop => write!(f, "nop"),
            MicroMirStatement::Set(t, p, m) => write!(f, "set {:?} -> {:?} ({:?})", t, p, m),
            MicroMirStatement::Move(p, t) => write!(f, "move {:?} -> {:?}", p, t),
            MicroMirStatement::Duplicate(p, t, m) => write!(f, "dup {:?} -> {:?} ({:?})", p, t, m),
            MicroMirStatement::Constant(k, t) => write!(f, "constant {:?} -> {:?}", k, t),
            MicroMirStatement::Kill(pls, LinearResource::Tmp(t)) => {
                write!(f, "kill ({:?}) {:?}", pls, t)
            }
            MicroMirStatement::Kill(pls, LinearResource::Mir(p)) => {
                write!(f, "kill ({:?}) {:?}", pls, p)
            }
            MicroMirStatement::NullOp(op, t) => write!(f, "op0 {:?} -> {:?}", op, t),
            MicroMirStatement::UnOp(op, t1, t2) => write!(f, "op1 {:?} {:?} -> {:?}", op, t1, t2),
            MicroMirStatement::BinaryOp(op, false, t1, t2, t3) => {
                write!(f, "op2 {:?} {:?} {:?} -> {:?}", t1, op, t2, t3)
            }
            MicroMirStatement::BinaryOp(op, true, t1, t2, t3) => {
                write!(f, "op2 checked {:?} {:?} {:?} -> {:?}", t1, op, t2, t3)
            }
            MicroMirStatement::Len(p, t, m) => write!(f, "len {:?} -> {:?} ({:?})", p, t, m),
            MicroMirStatement::Pack(ps, p) => write!(f, "pack {:?} -> {:?}", ps, p),
            MicroMirStatement::Unpack(p, ps) => write!(f, "unpack {:?} -> {:?}", p, ps),
            MicroMirStatement::Allocate(p) => write!(f, "alloc {:?}", p),
            MicroMirStatement::Deallocate(p) => write!(f, "dealloc {:?}", p),
            MicroMirStatement::Aggregate(p, subpermissions, m) => {
                write!(f, "aggregate ({:?}) ", m)?;
                for perm in subpermissions.iter() {
                    write!(f, "{:?}, ", perm)?;
                }
                write!(f, "-> {:?}", p)
            }
        }
    }
}

impl<'tcx> Debug for MicroMirTerminator<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Jump(bb) => write!(f, "jump {:?}", bb),
            Self::JumpInt(t, cond, m) => write!(f, "jumpInt {:?}:{:?} ({:?})", t, cond, m),
            Self::Return(m) => write!(f, "return ({:?})", m),
            Self::FailVerif => write!(f, "fail"),
        }
    }
}
