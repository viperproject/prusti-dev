// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    syntax::{LinearResource, PCSPermissionKind, PCS},
    util::*,
};
use itertools::Itertools;
use prusti_interface::{
    environment::Environment,
    utils::{expand_one_level, is_prefix},
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::{stable_map::FxHashMap, stable_set::FxHashSet},
    errors::MultiSpan,
    middle::mir::{Body, Local, Place},
};

// Assumption: All places are mutably owned
#[derive(Debug)]
pub struct PCSRepacker<'tcx> {
    pub packs: Vec<(Place<'tcx>, FxHashSet<Place<'tcx>>)>,
    pub unpacks: Vec<(Place<'tcx>, FxHashSet<Place<'tcx>>)>,
}

// TODO: Look over this again, many places need improvement
pub fn unify_moves<'mir, 'env: 'mir, 'tcx: 'env>(
    a_pcs: &PCS<'tcx>,
    b_pcs: &PCS<'tcx>,
    mir: &'mir Body<'tcx>,
    env: &'env Environment<'tcx>,
) -> EncodingResult<PCSRepacker<'tcx>> {
    let mut mir_problems: FxHashMap<
        (Local, PCSPermissionKind),
        (FxHashSet<Place<'tcx>>, FxHashSet<Place<'tcx>>),
    > = FxHashMap::default();

    // Split the problem into independent parts
    for pcs_permission in a_pcs.set.iter() {
        let permissionkind = pcs_permission.kind.clone();
        match pcs_permission.target {
            LinearResource::Mir(place) => {
                let local = place.local.clone();
                let set_borrow = mir_problems
                    .entry((local, permissionkind))
                    .or_insert((FxHashSet::default(), FxHashSet::default()));
                (*set_borrow).0.insert(place.clone());
            }
            LinearResource::Tmp(_) => {
                // Not changed by packs/unpacks
            }
        }
    }

    // TODO: DRY

    for pcs_permission in b_pcs.set.iter() {
        let permissionkind = pcs_permission.kind.clone();
        match pcs_permission.target {
            LinearResource::Mir(place) => {
                let local = place.local.clone();
                let set_borrow = mir_problems
                    .entry((local, permissionkind))
                    .or_insert((FxHashSet::default(), FxHashSet::default()));
                (*set_borrow).1.insert(place.clone());
            }
            LinearResource::Tmp(_) => {
                // Not changed by packs/unpacks
            }
        }
    }

    let mut a_unpacks: Vec<(Place<'tcx>, FxHashSet<Place<'tcx>>)> = Vec::default();
    let mut b_unpacks: Vec<(Place<'tcx>, FxHashSet<Place<'tcx>>)> = Vec::default();

    // Iterate over subproblems (in any order)
    let mut mir_problem_iter = mir_problems.drain();
    while let Some(((_local, _kind), (mut set_rc_a, mut set_rc_b))) = mir_problem_iter.next() {
        // No work to be done when PCS a is a subset of PCS b
        while !set_rc_b.is_subset(&set_rc_a) {
            // Remove intersection (b still not subset of a afterwards)
            let mut intersection: FxHashSet<Place<'tcx>> = FxHashSet::default();
            for x in set_rc_a.intersection(&set_rc_b) {
                intersection.insert(x.clone());
            }
            for x in intersection.into_iter() {
                set_rc_a.remove(&x);
                set_rc_b.remove(&x);
            }

            let mut gen_a: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut kill_a: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut gen_b: FxHashSet<Place<'tcx>> = FxHashSet::default();
            let mut kill_b: FxHashSet<Place<'tcx>> = FxHashSet::default();
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
                b_unpacks.push((*b, gen_b.clone()));
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
                a_unpacks.push((*a, gen_a.clone()));
            } else {
                return Err(PrustiError::internal(
                    format!(
                        "could not unify pcs's {:#?} and {:#?}",
                        a_pcs.set, b_pcs.set
                    ),
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

    Ok(PCSRepacker {
        unpacks: a_unpacks,
        packs: b_unpacks,
    })
}
