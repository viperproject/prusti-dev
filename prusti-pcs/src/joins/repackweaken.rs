// © 2021, ETH Zurich

//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
use crate::{
    syntax::{
        LinearResource, MicroMirStatement, MicroMirStatement::*, PCSPermission, PCSPermissionKind,
        PCSPermissionKind::*, PCS,
    },
    util::{EncodingResult, *},
};
use analysis::mir_utils::expand_struct_place;
use core::cell::*;
use itertools::{
    Either::{Left, Right},
    Itertools,
};
use prusti_interface::{
    environment::{
        borrowck::facts::{BorrowckFacts, Loan, PointType},
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
        mir_body::borrowck::facts::{
            LocationTable,
            RichLocation::{Mid, Start},
        },
        polonius_info::PoloniusInfo,
        Environment, Procedure,
    },
    utils::{expand_one_level, is_prefix},
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    middle::{
        mir,
        mir::{
            AggregateKind::*, Body, Local, Mutability, Operand, Operand::*, Place, Rvalue::*,
            StatementKind::*, Terminator, TerminatorKind, TerminatorKind::*,
        },
        ty::TyCtxt,
    },
};

// interp. Perfrom these in sequence.
#[derive(Debug)]
pub struct RepackWeaken<'tcx> {
    pub exclusive_unpack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    pub exclusive_pack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)>,
    pub exclusive_weaken: FxHashSet<mir::Place<'tcx>>,
    pub uninit_unpack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    pub uninit_pack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)>,
}

// Take two PCS's CUR, NEXT
//
// We have the following FREE PCS operations at our disposal
//  { unpack (e p) ...} { e p ...}        PACK   (unpack (e p)) (e p)
//  { e p ...} { unpack (e p) ...}        UNPACK (e p) (unpack (e p))
//  { e p } { u p }                       WEAKEN (e p)          (u p)
//
// The algorithm is as follows:
//      1. Turn the two PCS's into their most unpacked state
//           for uninit perms only ~> PACK + (reverse PACK)
//      2. Check for any weakening situations (required but not given)
//      2.5. Add uninit requirements to exclusive problem's postcondition
//      3. Turn the two PCS's into their most unpack state for
//          exclusive places only
//
//
// The string of generated annotations must be coherent and it's result
// should contain pcs_to

#[derive(Clone, Debug)]
pub struct PermissionSet<'tcx>(FxHashSet<PCSPermission<'tcx>>);

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

// TO DO NEXT:
//   Encode to the actual list of Free statements with pcs across them
//   Add in runtime init check (hopefully does nothing but might be needed for
//      init at loop heads and joins (or maybe just use them at join points lmfao))
//  Check coherence on examples
impl<'tcx> RepackWeaken<'tcx> {
    pub fn repack_weaken<'mir, 'env: 'mir>(
        // Context
        tcx: TyCtxt<'tcx>,
        mir: &'mir mir::Body<'tcx>,
        env: &'env Environment<'tcx>,
        // Repack pcs_from into pcs_to
        mut pcs_from: PermissionSet<'tcx>,
        mut pcs_to: PermissionSet<'tcx>,
    ) -> Self
    where
        'tcx: 'env,
    {
        let mut uninit_problems: FxHashMap<
            mir::Local,
            (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
        > = FxHashMap::default();

        // Setup the problem
        for place in pcs_from.0.iter().filter_map(|perm| {
            if let PCSPermissionKind::Uninit = perm.kind {
                if let LinearResource::Mir(p) = perm.target {
                    Some(p)
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = uninit_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert(place.clone());
        }

        for place in pcs_to.0.iter().filter_map(|perm| {
            if let PCSPermissionKind::Uninit = perm.kind {
                if let LinearResource::Mir(p) = perm.target {
                    Some(p)
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = uninit_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Repack the exclusive permissions
        let mut uninit_pack_stack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)> =
            Vec::default();
        let mut uninit_unpack_stack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();

        // Weakening requirements
        let mut uninit_weakenings: FxHashSet<mir::Place> = FxHashSet::default();

        let mut uninit_problem_iter = uninit_problems.drain();
        while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = uninit_problem_iter.next() {
            // Work until b is a subset of a
            while !set_rc_b.is_subset(&set_rc_a) {
                // Remove intersection (b still not subset of a afterwards)
                let mut intersection: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                for x in set_rc_a.intersection(&set_rc_b) {
                    intersection.insert(x.clone());
                }
                for x in intersection.into_iter() {
                    set_rc_a.remove(&x);
                    set_rc_b.remove(&x);
                }

                let mut gen_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut gen_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**a, **b))
                    .next()
                {
                    // println!("(1) {:#?} is a prefix of {:#?}", b, a);
                    // expand b
                    let (expand_b, remainder_b) =
                        expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                    gen_b = remainder_b.into_iter().collect();
                    gen_b.insert(expand_b);
                    kill_b = FxHashSet::from_iter([*b].into_iter());
                    uninit_pack_stack.push((gen_b.iter().cloned().collect(), *b));
                } else if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**b, **a))
                    .next()
                {
                    // println!("(2) {:#?} is a prefix of {:#?}", a, b);
                    // expand a
                    let (expand_a, remainder_a) =
                        expand_one_level(mir, env.tcx(), (*a).into(), (*b).into());
                    gen_a = remainder_a.into_iter().collect();
                    gen_a.insert(expand_a);
                    kill_a = FxHashSet::from_iter([*a].into_iter());
                    uninit_unpack_stack.push((*a, gen_a.iter().cloned().collect()));
                } else {
                    //  There are no elements which can be packed and unpacked anymore, but
                    //   nevertheless set_rc_b is not a subset of set_rc_a.
                    // We must weaken away all remaining permissions in set_rc_b
                    uninit_weakenings = set_rc_b.clone();
                    kill_b = set_rc_b.clone();
                }

                // Apply the gen/kill operations for this iteration

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

        // Set up exclusive problems
        let mut ex_problems: FxHashMap<
            mir::Local,
            (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
        > = FxHashMap::default();

        // Setup the problem
        for place in pcs_from.0.iter().filter_map(|perm| {
            if let Exclusive = perm.kind {
                if let LinearResource::Mir(p) = perm.target {
                    Some(p)
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert(place.clone());
        }

        for place in pcs_to.0.iter().filter_map(|perm| {
            if let Exclusive = perm.kind {
                if let LinearResource::Mir(p) = perm.target {
                    Some(p)
                } else {
                    None
                }
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Add weakening to the exclusive problem requirements
        for place in uninit_weakenings.iter() {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Solve the exclusive problem
        let mut ex_pack_stack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)> =
            Vec::default();
        let mut ex_unpack_stack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();

        let mut ex_problem_iter = ex_problems.drain();
        while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = ex_problem_iter.next() {
            // Work until b is a subset of a
            while !set_rc_b.is_subset(&set_rc_a) {
                // Remove intersection (b still not subset of a afterwards)
                let mut intersection: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                for x in set_rc_a.intersection(&set_rc_b) {
                    intersection.insert(x.clone());
                }
                for x in intersection.into_iter() {
                    set_rc_a.remove(&x);
                    set_rc_b.remove(&x);
                }

                let mut gen_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut gen_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**a, **b))
                    .next()
                {
                    // println!("(1) {:#?} is a prefix of {:#?}", b, a);
                    // expand b
                    let (expand_b, remainder_b) =
                        expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                    gen_b = remainder_b.into_iter().collect();
                    gen_b.insert(expand_b);
                    kill_b = FxHashSet::from_iter([*b].into_iter());
                    ex_pack_stack.push((gen_b.iter().cloned().collect(), *b));
                } else if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**b, **a))
                    .next()
                {
                    // println!("(2) {:#?} is a prefix of {:#?}", a, b);
                    // expand a
                    let (expand_a, remainder_a) =
                        expand_one_level(mir, env.tcx(), (*a).into(), (*b).into());
                    gen_a = remainder_a.into_iter().collect();
                    gen_a.insert(expand_a);
                    kill_a = FxHashSet::from_iter([*a].into_iter());
                    ex_unpack_stack.push((*a, gen_a.iter().cloned().collect()));
                } else {
                    // This should never happen if the semantics are sound
                    println!("Unsoundess: missing {:?}", set_rc_b);
                    panic!();
                }

                // Apply the gen/kill operations for this iteration

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

        // println!("REPACKING {:?} to {:?}", pcs_from, pcs_to);

        RepackWeaken {
            exclusive_unpack: ex_unpack_stack,
            exclusive_pack: ex_pack_stack.into_iter().rev().collect(),
            exclusive_weaken: uninit_weakenings,
            uninit_unpack: uninit_unpack_stack,
            uninit_pack: uninit_pack_stack.into_iter().rev().collect(),
        }
    }

    pub fn apply_as_seq_join(
        &self,
        working_pcs: &mut PCS<'tcx>,
        statements: &mut Vec<MicroMirStatement<'tcx>>,
        pcs_before: &mut Vec<PCS<'tcx>>,
    ) {
        // 1. EXCLUSIVE UNPACKS
        for (pre, post) in self.exclusive_unpack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = PCSPermission::new_initialized(Mutability::Mut, (*pre).into());
            let add = (*post)
                .iter()
                .map(|p| PCSPermission::new_initialized(Mutability::Mut, (*p).into()))
                .collect::<Vec<_>>();
            assert!(working_pcs.free.remove(&remove));
            for p in add.iter() {
                assert!(working_pcs.free.insert((*p).clone()));
            }
            statements.push(Unpack(*pre, post.iter().cloned().collect::<Vec<_>>()));
        }

        // 2. EXCLUSIVE PACKS
        for (pre, post) in self.exclusive_pack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = (*pre)
                .iter()
                .map(|p| PCSPermission::new_initialized(Mutability::Mut, (*p).into()))
                .collect::<Vec<_>>();
            let add = PCSPermission::new_initialized(Mutability::Mut, (*post).into());
            for p in remove.iter() {
                assert!(working_pcs.free.remove(p));
            }
            assert!(working_pcs.free.insert(add.clone()));

            statements.push(Pack(pre.iter().cloned().collect::<Vec<_>>(), *post));
        }

        // 3. WEAKEN
        for to_weaken in self.exclusive_weaken.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = PCSPermission::new_initialized(Mutability::Mut, (*to_weaken).into());
            let add = PCSPermission::new_uninit((*to_weaken).into());
            assert!(working_pcs.free.remove(&remove));
            assert!(working_pcs.free.insert(add.clone()));
            statements.push(Weaken(remove, add));
        }

        // 4. UNINIT UNPACKS
        for (pre, post) in self.uninit_unpack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = PCSPermission::new_uninit((*pre).into());
            let add = (*post)
                .iter()
                .map(|p| PCSPermission::new_uninit((*p).into()))
                .collect::<Vec<_>>();
            assert!(working_pcs.free.remove(&remove));
            for p in add.iter() {
                assert!(working_pcs.free.insert((*p).clone()));
            }
            statements.push(Unpack(*pre, post.iter().cloned().collect::<Vec<_>>()));
        }

        // 5. UNINIT PACKS
        for (pre, post) in self.uninit_pack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = (*pre)
                .iter()
                .map(|p| PCSPermission::new_uninit((*p).into()))
                .collect::<Vec<_>>();
            let add = PCSPermission::new_uninit((*post).into());
            for p in remove.iter() {
                assert!(working_pcs.free.remove(p));
            }
            assert!(working_pcs.free.insert(add.clone()));
            statements.push(Pack(pre.iter().cloned().collect::<Vec<_>>(), *post));
        }
    }
}
