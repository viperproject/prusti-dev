// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::mir_encoder::MirEncoder;
/// Module that allows querying the initialisation information.
use prusti_common::vir;
use prusti_interface::environment::mir_analyses::initialization::compute_definitely_initialized;
use prusti_interface::environment::place_set::PlaceSet;
use rustc::hir::def_id::DefId;
use rustc::{mir, ty};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use encoder::errors::ErrorCtxt;

pub struct InitInfo {
    //mir_acc_before_block: HashMap<mir::BasicBlock, HashSet<mir::Place<'tcx>>>,
    //mir_acc_after_statement: HashMap<mir::Location, HashSet<mir::Place<'tcx>>>,
    vir_acc_before_block: HashMap<mir::BasicBlock, HashSet<vir::Expr>>,
    vir_acc_after_statement: HashMap<mir::Location, HashSet<vir::Expr>>,
}

/// Create a set that contains all places and their prefixes of the original set.
fn explode<'tcx>(place_set: PlaceSet<'tcx>) -> HashSet<mir::Place<'tcx>> {
    let mut result = HashSet::new();
    fn insert<'tcx>(place: mir::Place<'tcx>, set: &mut HashSet<mir::Place<'tcx>>) {
        match place {
            mir::Place::Local(_) => {}
            mir::Place::Static(_) => {}
            mir::Place::Projection(box mir::Projection { ref base, .. }) => {
                insert(base.clone(), set)
            }
        }
        set.insert(place);
    }
    for place in place_set.into_iter() {
        insert(place, &mut result);
    }
    result
}

/// Does the ``set`` contain the ``place`` or its prefix?
fn contains_prefix(set: &HashSet<vir::Expr>, place: &vir::Expr) -> bool {
    if set.contains(place) {
        true
    } else if let Some(parent) = place.get_parent_ref() {
        contains_prefix(set, parent)
    } else {
        false
    }
}

fn convert_to_vir<'tcx, T: Eq + Hash + Clone>(
    map: &HashMap<T, HashSet<mir::Place<'tcx>>>,
    mir_encoder: &MirEncoder<'_, '_, '_, 'tcx, '_>,
) -> Result<HashMap<T, HashSet<vir::Expr>>, ErrorCtxt> {
    map.iter()
        .map(|(loc, set)| {
            let new_set: Result<HashSet<vir::Expr>, ErrorCtxt> = set
                .iter()
                .map(|place| {
                    match mir_encoder.encode_place(place) {
                        Err(error) => Err(error),
                        Ok(result) => Ok(result.0)
                    }
                })
                .collect();
            match new_set {
                Err(error) => Err(error),
                Ok(result) => Ok((loc.clone(), result))
            }
        })
        .collect()
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> InitInfo {
    pub fn new(
        mir: &'p mir::Mir<'tcx>,
        tcx: ty::TyCtxt<'p, 'tcx, 'tcx>,
        def_id: DefId,
        mir_encoder: &MirEncoder<'p, 'v, 'r, 'a, 'tcx>,
    ) -> Result<Self, ErrorCtxt> {
        let def_path = tcx.hir.def_path(def_id);
        let initialisation = compute_definitely_initialized(&mir, tcx, def_path);
        let mir_acc_before_block: HashMap<_, _> = initialisation
            .before_block
            .into_iter()
            .map(|(basic_block, place_set)| (basic_block, explode(place_set)))
            .collect();
        let mir_acc_after_statement: HashMap<_, _> = initialisation
            .after_statement
            .into_iter()
            .map(|(location, place_set)| (location, explode(place_set)))
            .collect();
        let vir_acc_before_block = convert_to_vir(&mir_acc_before_block, mir_encoder)?;
        let vir_acc_after_statement = convert_to_vir(&mir_acc_after_statement, mir_encoder)?;
        Ok(Self {
            //mir_acc_before_block,
            //mir_acc_after_statement,
            vir_acc_before_block,
            vir_acc_after_statement,
        })
    }

    /// Is the ``place`` accessible (it is a prefix of a definitely
    /// initalised place) before the statement at given `location`?
    pub fn is_vir_place_accessible(&self, place: &vir::Expr, location: mir::Location) -> bool {
        if location.statement_index == 0 {
            contains_prefix(&self.vir_acc_before_block[&location.block], place)
        } else {
            let new_location = mir::Location {
                statement_index: location.statement_index - 1,
                ..location
            };
            contains_prefix(&self.vir_acc_after_statement[&new_location], place)
        }
    }
}
