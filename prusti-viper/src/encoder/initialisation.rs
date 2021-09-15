// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
/// Module that allows querying the initialisation information.
use vir_crate::polymorphic as vir;
use prusti_interface::environment::mir_analyses::initialization::compute_definitely_initialized;
use prusti_interface::environment::place_set::PlaceSet;
use prusti_interface::utils::expand_one_level;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty::{self, TyCtxt}};
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use crate::encoder::errors::{SpannedEncodingError, EncodingError};
use crate::encoder::errors::EncodingResult;
use crate::encoder::errors::SpannedEncodingResult;

pub struct InitInfo {
    //mir_acc_before_block: HashMap<mir::BasicBlock, HashSet<mir::Place<'tcx>>>,
    //mir_acc_after_statement: HashMap<mir::Location, HashSet<mir::Place<'tcx>>>,
    vir_acc_before_block: HashMap<mir::BasicBlock, HashSet<vir::Expr>>,
    vir_acc_after_statement: HashMap<mir::Location, HashSet<vir::Expr>>,
}

/// Create a set that contains all places and their prefixes of the original set.
fn explode<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place_set: PlaceSet<'tcx>
) -> HashSet<mir::Place<'tcx>> {
    let mut result = HashSet::new();
    for guide_place in place_set.into_iter() {
        let mut current_place: mir::Place = guide_place.local.into();
        result.insert(current_place);
        while current_place.projection.len() < guide_place.projection.len() {
            let (new_current_place, _) = expand_one_level(mir, tcx, current_place, guide_place);
            current_place = new_current_place;
            result.insert(new_current_place);
        }
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
    mir_encoder: &MirEncoder<'_, '_, 'tcx>,
) -> EncodingResult<HashMap<T, HashSet<vir::Expr>>> {
    let mut result = HashMap::new();
    for (loc, set) in map.iter() {
        let mut new_set = HashSet::new();
        for place in set.iter() {
            let encoded_place = mir_encoder.encode_place(place)?.0.try_into_expr()?;
            new_set.insert(encoded_place);
        }
        result.insert(loc.clone(), new_set);
    }
    Ok(result)
}

impl<'p, 'v: 'p, 'tcx: 'v> InitInfo {
    pub fn new(
        mir: &'p mir::Body<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        _def_id: DefId,
        mir_encoder: &MirEncoder<'p, 'v, 'tcx>,
    ) -> EncodingResult<Self> {
        let initialisation = compute_definitely_initialized(mir, tcx);
        let mir_acc_before_block: HashMap<_, _> = initialisation
            .before_block
            .into_iter()
            .map(|(basic_block, place_set)| (basic_block, explode(mir, tcx, place_set)))
            .collect();
        let mir_acc_after_statement: HashMap<_, _> = initialisation
            .after_statement
            .into_iter()
            .map(|(location, place_set)| (location, explode(mir, tcx, place_set)))
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
