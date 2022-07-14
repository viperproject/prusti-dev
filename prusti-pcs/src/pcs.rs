// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
#![allow(unused_imports)]

use crate::syntactic_expansion;
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
    FailVerif,
}

pub struct MicroMirData<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub terminator: MicroMirTerminator<'tcx>,
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

#[derive(Debug)]
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
}

pub trait HoareSemantics {
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
            MicroMirTerminator::FailVerif => None,
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
            MicroMirTerminator::FailVerif => None,
        }
    }
}

impl<'tcx> MicroMirBody<'tcx> {
    // pub fn statement_at(&self, location: Location) -> &MicroMirStatement {
    //     return &self.body[location.block].statements[location.statement_index];
    // }

    // pub fn terminator_of(&self, location: Location) -> &MicroMirTerminator {
    //     return &self.body[location.block].terminator;
    // }

    // pub fn terminator_of_bb(&self, bb: BasicBlock) -> &MicroMirTerminator {
    //     return &self.body[bb].terminator;
    // }

    // Read off the precondition for the core memory safety proof
    // INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    // INVARIANT: The final MicroMir has no preconditions that are NONE
    // pub fn core_precondition(&self, location: Location) -> Option<PCS> {
    //     self.statement_at(location).precondition()
    // }

    // Read off the precondition for the core memory safety proof
    // INVARIANT: This is never incorrect at any step in the elaboration (but can be NONE)
    // INVARIANT: The final MicroMir has no postconditions that are NONE
    // pub fn core_postcondition(&self, location: Location) -> Option<PCS> {
    //     self.statement_at(location).postcondition()
    // }
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
            MicroMirStatement::Kill(LinearResource::Tmp(t)) => write!(f, "kill {:?}", t),
            MicroMirStatement::Kill(LinearResource::Mir(p)) => write!(f, "kill {:?}", p),
            MicroMirStatement::NullOp(op, t) => write!(f, "op0 {:?} -> {:?}", op, t),
            MicroMirStatement::UnOp(op, t1, t2) => write!(f, "op1 {:?} {:?} -> {:?}", op, t1, t2),
            MicroMirStatement::BinaryOp(op, false, t1, t2, t3) => {
                write!(f, "op2 {:?} {:?} {:?} -> {:?}", t1, op, t2, t3)
            }
            MicroMirStatement::BinaryOp(op, true, t1, t2, t3) => {
                write!(f, "op2 checked {:?} {:?} {:?} -> {:?}", t1, op, t2, t3)
            }
            MicroMirStatement::Len(p, t, m) => write!(f, "len {:?} -> {:?} ({:?})", p, t, m),
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

pub fn dump_pcs<'tcx>(env: Environment<'tcx>) {
    for proc_id in env.get_annotated_procedures() {
        println!("id: {:#?}", env.get_unique_item_name(proc_id));
        let current_procedure = env.get_procedure(proc_id);
        let _mir = current_procedure.get_mir();

        // Q: Can we get the MIR?
        // let mir = env.local_mir(proc_id.expect_local(), env.identity_substs(proc_id));
        // println!("{:#?}", *mir);
        // Alternate:

        // Q: What about borrowck facts?
        // if let Some(facts) = env.try_get_local_mir_borrowck_facts(proc_id.expect_local()) {
        //     println!("{:#?}", (*facts).input_facts);
        // } else {
        //     println!("No borrowck facts");
        // }

        // Q: What kind of loop information can we get?
        // let loop_info = current_procedure.loop_info();
        // println!("\theads: {:#?}", loop_info.loop_heads);
        // println!("\thead depths: {:#?}", loop_info.loop_head_depths);

        // Q: MIR analyses?
    }
}

type EncodingResult<A> = Result<A, PrustiError>;

// Retrieves the underlying place for a linear resource, or reports an error
fn retrieve_place<'tcx>(p: &PCSPermission<'tcx>) -> EncodingResult<Place<'tcx>> {
    match p.target {
        LinearResource::Mir(pl) => Ok(pl),
        LinearResource::Tmp(_) => Err(PrustiError::internal(
            "can not retrive underlying place from temporary resource",
            MultiSpan::new(),
        )),
    }
}

fn retrieve_local_decl<'a, 'tcx: 'a>(
    mir: &'a Body<'tcx>,
    p: &'a Place<'tcx>,
) -> EncodingResult<&'a LocalDecl<'tcx>> {
    match mir.local_decls.get(p.local) {
        Some(decl) => Ok(decl),
        None => Err(PrustiError::internal(
            format!("error when retrieving local_decl for place {:#?}", p),
            MultiSpan::new(),
        )),
    }
}

struct PCSUnifier<'tcx> {
    packs: Vec<Place<'tcx>>,
    unpacks: Vec<Place<'tcx>>,
    packed_meet: FxHashSet<Place<'tcx>>,
}

// Packs performed in order (iterate)
// Unpacks performed in reverse order (pop)
// Well defined to just keep a list of places because temps can't be unified xd
// Result is packed_meet

// Constructs a sequence of packs and unpacks to unify two PCS's together, if it exists.
//  IDEA: PCS's naturally form a partial order
//                                P <= Q   Q <= R                 P <= Q   Q <= P
//          ---------- (refl)   ------------------- (trans)     ------------------- (antisym)
//            P <= P                  P <= R                            P = Q
//
//
//          -------------------- (packing)
//             unpack p <= {p}
//
//
//                P <= Q                          P superset of Q
//          ----------------- (framing)         ------------------- (sups)
//            P U R <= Q U R                         P <= Q
//
//      where the "union" of two PCS's is the separating union, if valid. That is, {f} U {f.g} is not allowed.
//
//      These rules imply that {} is the top of this partial order. There are several bottoms.
//
//
//
//  FACT: pack/unpack do not change base local or exlusivity
//          => Greatest meet can be computed individually for (base local)
//
//  FACT: If a sequence of packs/unpacks unify two PCS's, it can be written as a
//          sequence of unpacks followed by a sequence of packs
//          => Property of a lattice meet
//
// TODO: For now let us just assume that we're working with exclusive permissions.
fn unify_moves<'tcx>(
    a: FxHashSet<PCSPermission<'tcx>>,
    b: FxHashSet<PCSPermission<'tcx>>,
    mir: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> EncodingResult<()> {
    // Invariant: Each iteration only weakens a and b using the (packing) rule.
    // Termination: Well founded because the meet is well-defined for each place, then complete
    //      the argument with the framing rule (this right?)

    // 0. Split into smaller, independent problems
    let mut mir_problems: FxHashMap<
        (Local, PCSPermissionKind),
        (FxHashSet<Place<'tcx>>, FxHashSet<Place<'tcx>>),
    > = FxHashMap::default();

    // Checking temporaries is simple: They aren't allowed to pack/unpack
    //      so we just need to check that they have the same mutability
    let _tmp_problems: FxHashMap<TemporaryPlace, PCSPermissionKind> = FxHashMap::default();

    // Split the problem into independent parts
    for pcs_permission in a.clone().into_iter() {
        let permissionkind = pcs_permission.kind;
        match pcs_permission.target {
            LinearResource::Mir(place) => {
                let local = place.local.clone();
                let set_borrow = mir_problems
                    .entry((local, permissionkind))
                    .or_insert((FxHashSet::default(), FxHashSet::default()));
                (*set_borrow).0.insert(place.clone());
            }
            LinearResource::Tmp(_temp) => {
                todo!();
            }
        }
    }

    // TODO: DRY

    for pcs_permission in b.into_iter() {
        let permissionkind = pcs_permission.kind.clone();
        match pcs_permission.target {
            LinearResource::Mir(place) => {
                let local = place.local.clone();
                let set_borrow = mir_problems
                    .entry((local, permissionkind))
                    .or_insert((FxHashSet::default(), FxHashSet::default()));
                (*set_borrow).1.insert(place.clone());
            }
            LinearResource::Tmp(_temp) => {
                todo!();
            }
        }
    }

    let mut a_unpacks: Vec<Place<'tcx>> = Vec::default();
    let mut b_unpacks: Vec<Place<'tcx>> = Vec::default();

    // Iterate over subproblems (in any order)
    let mut mir_problem_iter = mir_problems.drain();
    while let Some(((_local, _kind), (mut set_rc_a, mut set_rc_b))) = mir_problem_iter.next() {
        loop {
            // Remove (mark?) elements which do not need to be considered.
            let mut intersection: FxHashSet<Place<'tcx>> = FxHashSet::default();
            for x in set_rc_a.intersection(&set_rc_b) {
                intersection.insert(x.clone());
            }
            for x in intersection.into_iter() {
                set_rc_a.remove(&x);
                set_rc_b.remove(&x);
            }

            // If no more elements in set, we are done (they're unified)
            if (set_rc_a.len() == 0) && (set_rc_b.len() == 0) {
                break;
            }

            let mut gen_a: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut kill_a: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut gen_b: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut kill_b: FxHashSet<Place<'tcx>> = FxHashSet::default();
            if let Some((a, _)) = set_rc_a
                .iter()
                .cartesian_product(set_rc_b.iter())
                .filter(|(a, b)| is_prefix(**a, **b))
                .next()
            {
                // b is a prefix of a => a should get expanded
                gen_a = FxHashSet::from_iter(expand_place(*a, mir, tcx)?);
                kill_a = FxHashSet::from_iter([*a].into_iter());
                a_unpacks.push(*a);
            } else if let Some((_, b)) = set_rc_a
                .iter()
                .cartesian_product(set_rc_b.iter())
                .filter(|(a, b)| is_prefix(**b, **a))
                .next()
            {
                // a is a prefix of b => b should get expanded
                gen_b = FxHashSet::from_iter(expand_place(*b, mir, tcx)?);
                kill_b = FxHashSet::from_iter([*b].into_iter());
                b_unpacks.push(*b);
            } else {
                return Err(PrustiError::internal(
                    format!("could not unify pcs's"),
                    MultiSpan::new(),
                ));
            }

            for a in kill_a.iter() {
                set_rc_a.remove(a);
            }

            for a in gen_a.iter() {
                set_rc_a.insert(*a);
            }

            for b in kill_b.iter() {
                set_rc_b.remove(b);
            }

            for b in gen_b.iter() {
                set_rc_b.insert(*b);
            }
        }
    }

    let mut working_pcs: FxHashSet<Place<'tcx>> = a
        .iter()
        .map(|perm| {
            if let LinearResource::Mir(p) = perm.target {
                p
            } else {
                panic!();
            }
        })
        .collect();

    for p in a_unpacks.iter() {
        if !working_pcs.remove(p) {
            return Err(PrustiError::internal(
                format!("prusti generated an incoherent unpack"),
                MultiSpan::new(),
            ));
        }
        for p1 in expand_place(*p, mir, tcx)? {
            if !working_pcs.insert(p1) {
                return Err(PrustiError::internal(
                    format!("prusti generated an incoherent unpack"),
                    MultiSpan::new(),
                ));
            }
        }
    }

    for p in b_unpacks.iter().rev() {
        if !working_pcs.remove(p) {
            return Err(PrustiError::internal(
                format!("prusti generated an incoherent pack"),
                MultiSpan::new(),
            ));
        }
        for p1 in expand_place(*p, mir, tcx)? {
            if !working_pcs.insert(p1) {
                return Err(PrustiError::internal(
                    format!("prusti generated an incoherent pack"),
                    MultiSpan::new(),
                ));
            }
        }
    }

    // At this point, we can check that b is a subset of the computed PCS.

    return Ok(());
}

/// Copied from analysis/mir_utils to properly handle errors and have the correct return type for this situation
fn expand_place<'tcx>(
    place: Place<'tcx>,
    mir: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> EncodingResult<Vec<Place<'tcx>>> {
    match place.projection[place.projection.len()] {
        mir::ProjectionElem::Field(projected_field, field_ty) => {
            let mut places = expand_struct_place(place, mir, tcx, Some(projected_field.index()));
            let new_current_place = tcx.mk_place_field(place, projected_field, field_ty).into();
            // TODO: Is this correct?
            places.push(new_current_place);
            Ok(places)
        }
        mir::ProjectionElem::Downcast(_symbol, variant) => {
            let kind = &place.ty(mir, tcx).ty.kind();
            if let ty::TyKind::Adt(adt, _) = kind {
                Ok(vec![tcx.mk_place_downcast(place, *adt, variant).into()])
            } else {
                Err(PrustiError::internal(
                    format!("unreachable state in expansion of downcast"),
                    MultiSpan::new(),
                ))
            }
        }
        mir::ProjectionElem::Deref => Ok(vec![tcx.mk_place_deref(place).into()]),
        mir::ProjectionElem::Index(idx) => Ok(vec![tcx.mk_place_index(place, idx).into()]),
        elem => Err(PrustiError::unsupported(
            format!("expansion of place {:#?} unsuppoted", elem),
            MultiSpan::new(),
        )),
    }
}

// TODO:
//
// - Place packing relation
//      Representation of the types as we need,
//          Precompute type relations?
//          New ADT for our types?
// - Finish packer with uninit/shared/temporary
//      Add checking of the final thing
//      Remove trash and refactor to something sensible
// - Graphviz dump
//
