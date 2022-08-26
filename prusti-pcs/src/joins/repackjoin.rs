// © 2021, ETH Zurich

//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
use crate::{
    joins::PermissionSet,
    pcs_analysis::conditional::StraightOperationalMir,
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
pub struct RepackJoin<'tcx> {
    pub ex_unpack_a: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    pub ex_weaken_a: FxHashSet<mir::Place<'tcx>>,
    pub un_unpack_a: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    pub ex_unpack_b: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    pub ex_weaken_b: FxHashSet<mir::Place<'tcx>>,
    pub un_unpack_b: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
}

impl<'tcx> RepackJoin<'tcx> {
    pub fn repack_join<'mir, 'env: 'mir>(
        // Context
        tcx: TyCtxt<'tcx>,
        mir: &'mir mir::Body<'tcx>,
        env: &'env Environment<'tcx>,
        // Repack pcs_from into pcs_to
        mut pcs_a: PermissionSet<'tcx>,
        mut pcs_b: PermissionSet<'tcx>,
    ) -> Self
    where
        'tcx: 'env,
    {
        let mut uninit_problems: FxHashMap<
            mir::Local,
            (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
        > = FxHashMap::default();

        // Setup the problem
        for place in pcs_a.0.iter().filter_map(|perm| {
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

        for place in pcs_b.0.iter().filter_map(|perm| {
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

        // Repack the uninit permissions
        let mut uninit_unpack_stack_a: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();
        let mut uninit_unpack_stack_b: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();

        // Weakening requirements
        let mut uninit_weakenings_a: FxHashSet<mir::Place> = FxHashSet::default();
        let mut uninit_weakenings_b: FxHashSet<mir::Place> = FxHashSet::default();

        println!("UNINIT PROBLEMS: {:?}", uninit_problems);

        let mut uninit_problem_iter = uninit_problems.drain();
        while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = uninit_problem_iter.next() {
            // Work until b equals a
            while set_rc_b != set_rc_a {
                // Remove intersection
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
                    // element of b is a prefix of an element of a
                    // expand b
                    let (expand_b, remainder_b) =
                        expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                    gen_b = remainder_b.into_iter().collect();
                    gen_b.insert(expand_b);
                    kill_b = FxHashSet::from_iter([*b].into_iter());
                    uninit_unpack_stack_b.push((*b, gen_b.iter().cloned().collect()));
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
                    uninit_unpack_stack_a.push((*a, gen_a.iter().cloned().collect()));
                } else {
                    //  There are no elements which can be packed and unpacked anymore, but
                    //   nevertheless set_rc_b is not a subset of set_rc_a.
                    // We must weaken away all remaining permissions
                    uninit_weakenings_b = set_rc_b.clone();
                    kill_b = set_rc_b.clone();

                    uninit_weakenings_a = set_rc_a.clone();
                    kill_a = set_rc_a.clone();
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
        for place in pcs_a.0.iter().filter_map(|perm| {
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

        for place in pcs_b.0.iter().filter_map(|perm| {
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

        println!("PRE EX PROBLEMS: {:?}", ex_problems);

        // Add weakening to the exclusive problem requirements
        for place in uninit_weakenings_a.iter() {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert(place.clone());
        }

        for place in uninit_weakenings_b.iter() {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        println!("EX PROBLEMS: {:?}", ex_problems);

        // Solve the exclusive problem
        let mut ex_unpack_stack_a: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();
        let mut ex_unpack_stack_b: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
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
                    ex_unpack_stack_b.push((*b, gen_b.iter().cloned().collect()));
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
                    ex_unpack_stack_a.push((*a, gen_a.iter().cloned().collect()));
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

        RepackJoin {
            ex_unpack_a: ex_unpack_stack_a,
            ex_weaken_a: uninit_weakenings_a,
            un_unpack_a: uninit_unpack_stack_a,
            ex_unpack_b: ex_unpack_stack_b,
            ex_weaken_b: uninit_weakenings_b,
            un_unpack_b: uninit_unpack_stack_b,
        }
    }

    pub fn apply_join(
        &self,
        op_a: &mut StraightOperationalMir<'tcx>,
        mut working_pcs_a: PCS<'tcx>,
        op_b: &mut StraightOperationalMir<'tcx>,
        mut working_pcs_b: PCS<'tcx>,
    ) -> PCS<'tcx> {
        Self::do_apply(
            self.ex_unpack_a.clone(),
            self.ex_weaken_a.clone(),
            self.un_unpack_a.clone(),
            &mut working_pcs_a,
            &mut op_a.statements,
            &mut op_b.pcs_before,
        );
        Self::do_apply(
            self.ex_unpack_b.clone(),
            self.ex_weaken_b.clone(),
            self.un_unpack_b.clone(),
            &mut working_pcs_b,
            &mut op_b.statements,
            &mut op_b.pcs_before,
        );

        assert!(working_pcs_a == working_pcs_b);
        working_pcs_a
    }

    fn do_apply(
        ex_unpacks: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
        weakenings: FxHashSet<mir::Place<'tcx>>,
        un_unpacks: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
        working_pcs: &mut PCS<'tcx>,
        statements: &mut Vec<MicroMirStatement<'tcx>>,
        pcs_before: &mut Vec<PCS<'tcx>>,
    ) {
        // Try to figure out what's going wrong at this point
        println!("============= REPACK JOIN =============");
        println!("Applying ex_unpk {:?}", ex_unpacks);
        println!("Applying weakening {:?}", weakenings);
        println!("Applying un_unpacks {:?}", un_unpacks);
        println!("=======================================");

        // 1. EXCLUSIVE UNPACKS
        for (pre, post) in ex_unpacks.iter() {
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

        // 2. WEAKEN
        for to_weaken in weakenings.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = PCSPermission::new_initialized(Mutability::Mut, (*to_weaken).into());
            let add = PCSPermission::new_uninit((*to_weaken).into());
            assert!(working_pcs.free.remove(&remove));
            assert!(working_pcs.free.insert(add.clone()));
            statements.push(Weaken(remove, add));
        }

        // 3. UNINIT UNPACKS
        for (pre, post) in un_unpacks.iter() {
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
    }
}
