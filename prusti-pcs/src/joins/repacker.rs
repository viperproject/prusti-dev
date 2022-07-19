// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    syntax::{LinearResource, MicroMirStatement, PCSPermissionKind, TemporaryPlace, PCS},
    util::*,
};
use itertools::Itertools;
use prusti_interface::{environment::Environment, utils::is_prefix, PrustiError};
use prusti_rustc_interface::{
    data_structures::{stable_map::FxHashMap, stable_set::FxHashSet},
    errors::MultiSpan,
    middle::{
        mir::{Body, Local, Place},
        ty::TyCtxt,
    },
};

// Assumption: All places are mutably owned
pub struct PCSRepacker<'tcx> {
    pub packs: Vec<Place<'tcx>>,
    pub unpacks: Vec<Place<'tcx>>,
}

// TODO: Look over this again, many places need improvement
pub fn unify_moves<'mir, 'env: 'mir, 'tcx: 'env>(
    a_pcs: &PCS<'tcx>,
    b_pcs: &PCS<'tcx>,
    mir: &'mir Body<'tcx>,
    env: &'env Environment<'tcx>,
) -> EncodingResult<PCSRepacker<'tcx>> {
    // let a = a_pcs.set.clone();
    // let b = b_pcs.set.clone();

    let mut mir_problems: FxHashMap<
        (Local, PCSPermissionKind),
        (FxHashSet<Place<'tcx>>, FxHashSet<Place<'tcx>>),
    > = FxHashMap::default();

    // Checking temporaries is simple: They aren't allowed to pack/unpack
    //      so we just need to check that they have the same mutability
    let _tmp_problems: FxHashMap<TemporaryPlace, PCSPermissionKind> = FxHashMap::default();

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
            LinearResource::Tmp(_temp) => {
                todo!();
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
                gen_a = FxHashSet::from_iter(expand_place(*a, mir, env)?);
                kill_a = FxHashSet::from_iter([*a].into_iter());
                a_unpacks.push(*a);
            } else if let Some((_, b)) = set_rc_a
                .iter()
                .cartesian_product(set_rc_b.iter())
                .filter(|(a, b)| is_prefix(**b, **a))
                .next()
            {
                // a is a prefix of b => b should get expanded
                gen_b = FxHashSet::from_iter(expand_place(*b, mir, env)?);
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

    // let mut working_pcs: FxHashSet<Place<'tcx>> = a
    //     .iter()
    //     .map(|perm| {
    //         if let LinearResource::Mir(p) = perm.target {
    //             p
    //         } else {
    //             panic!();
    //         }
    //     })
    //     .collect();

    // At this point, we can check that b is a subset of the computed PCS.

    return Ok(PCSRepacker {
        unpacks: a_unpacks,
        packs: b_unpacks,
    });
}

impl<'tcx> PCSRepacker<'tcx> {
    pub fn encode<'env>(
        &self,
        env: &'env Environment,
    ) -> EncodingResult<Vec<MicroMirStatement<'tcx>>>
    where
        'tcx: 'env,
    {
        todo!();
    }
}
/*
    let mut ret: Vec<MicroMirStatement<'tcx>> = vec![];
    for upk in self.unpacks.iter() {
        ret.push(MicroMirStatement::Unpack(
            *upk,
            expand_place(*upk, mir, tcx)?,
        ));
    }
    for pk in self.packs.iter().rev() {
        ret.push(MicroMirStatement::Pack(expand_place(*pk, mir, tcx)?, *pk));
    }
    return Ok(ret);
}
*/

// pub fn separating_union<'tcx>(a: PCS<'tcx>, b: PCS<'tcx>) -> EncodingResult<PCS<'tcx>> {
//     // Naive solution
//     for b in b.set.iter() {
//         for a in a.set.iter() {
//             match (a.target, b.target) {
//                 (Mir(pa), Mir(pb)) => {
//                     todo!();
//                 }
//                 (Tmp(pa), Tmp(pb)) => {
//                     todo!();
//                 }
//             }
//
//             // match ((a.kind, b.kind)) {
//             //     (_, Shared) | (Shared, _) => {
//             //         return Err(PrustiError::internal(
//             //             "shared permissions not implemented",
//             //             MultiSpan::new(),
//             //         ));
//             //     },
//
//             //     }
//
//             // }
//             // if is_prefix(a, b) || is_prefix(b, a) {
//             //     return Err(PrustiError::internal(
//             //         "separating union between two PCS's failed",
//             //         MultiSpan::new(),
//             //     ));
//             // }
//         }
//     }
//
//     todo!();
// }
//
