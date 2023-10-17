// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod edge;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, Borrows, OutlivesConstraint, PoloniusInput, RustcFacts},
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{
            Body, ConstraintCategory, Local, Location, Operand, Place, StatementKind,
            TerminatorKind, RETURN_PLACE,
        },
        ty::{RegionVid, Ty, TyCtxt},
    },
};

use super::region_info::RegionInfo;

#[derive(Debug)]
pub struct OutlivesInfo<'tcx> {
    pub universal_local_constraints: Vec<OutlivesConstraint<'tcx>>,
    pub local_constraints: Vec<OutlivesConstraint<'tcx>>, // but with no location info
    pub type_ascription_constraints: Vec<OutlivesConstraint<'tcx>>,
    pub location_constraints: FxHashMap<Location, Vec<OutlivesConstraint<'tcx>>>,
    pub universal_constraints: Vec<(RegionVid, RegionVid)>,
}

impl<'tcx> OutlivesInfo<'tcx> {
    pub fn new(
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2<'tcx>,
        ri: &RegionInfo<'tcx>,
    ) -> Self {
        let mut universal_constraints =
            FxHashSet::from_iter(input_facts.known_placeholder_subset.iter().copied());

        let mut universal_local_constraints = Vec::new();
        let mut local_constraints = Vec::new();
        let mut type_ascription_constraints = Vec::new();
        let mut location_constraints: FxHashMap<Location, Vec<OutlivesConstraint<'tcx>>> =
            FxHashMap::default();
        for constraint in facts2.region_inference_context.outlives_constraints() {
            if let Some(loc) = constraint.locations.from_location() {
                location_constraints
                    .entry(loc)
                    .or_default()
                    .push(constraint);
            } else if ri.map.is_universal(constraint.sup) || ri.map.is_universal(constraint.sub) {
                if ri.map.is_universal(constraint.sup) && ri.map.is_universal(constraint.sub) {
                    // Not sure why the `region_inference_context` can rarely contain inter-universal constraints,
                    // but we should already have all of these in `universal_constraints`.
                    // Except for even more rare situations...
                    universal_constraints.insert((constraint.sup, constraint.sub));
                } else {
                    universal_local_constraints.push(constraint);
                }
            } else if matches!(constraint.category, ConstraintCategory::TypeAnnotation) {
                type_ascription_constraints.push(constraint);
            } else {
                local_constraints.push(constraint);
            }
        }
        Self {
            universal_local_constraints,
            local_constraints,
            type_ascription_constraints,
            location_constraints,
            universal_constraints: universal_constraints.into_iter().collect(),
        }
    }

    fn location(&self, location: Location) -> &[OutlivesConstraint<'tcx>] {
        self.location_constraints
            .get(&location)
            .map_or(&[], |v| v.as_slice())
    }
    // #[tracing::instrument(name = "OutlivesInfo::pre_constraints", level = "debug", skip(self, ri))]
    pub fn pre_constraints<'a>(
        &'a self,
        location: Location,
        local: Option<Local>,
        ri: &'a RegionInfo<'tcx>,
    ) -> impl Iterator<Item = &OutlivesConstraint<'tcx>> + 'a {
        self.location(location).iter().filter(move |c| {
            if let Some(local) = local {
                ri.map
                    .get(c.sub)
                    .get_place()
                    .map(|l| l != local)
                    .unwrap_or(true)
                    && ri
                        .map
                        .get(c.sup)
                        .get_place()
                        .map(|l| l != local)
                        .unwrap_or(true)
            } else {
                true
            }
        })
    }
    // #[tracing::instrument(name = "OutlivesInfo::pre_constraints", level = "debug", skip(self, ri))]
    pub fn post_constraints<'a>(
        &'a self,
        location: Location,
        local: Option<Local>,
        ri: &'a RegionInfo<'tcx>,
    ) -> impl Iterator<Item = &OutlivesConstraint<'tcx>> + 'a {
        self.location(location).iter().filter(move |c| {
            !(if let Some(local) = local {
                ri.map
                    .get(c.sub)
                    .get_place()
                    .map(|l| l != local)
                    .unwrap_or(true)
                    && ri
                        .map
                        .get(c.sup)
                        .get_place()
                        .map(|l| l != local)
                        .unwrap_or(true)
            } else {
                true
            })
        })
    }
}

pub trait AssignsToPlace<'tcx> {
    fn assigns_to(&self) -> Option<Place<'tcx>>;
}

impl<'tcx> AssignsToPlace<'tcx> for StatementKind<'tcx> {
    fn assigns_to(&self) -> Option<Place<'tcx>> {
        match self {
            StatementKind::Assign(box (place, _)) => Some(*place),
            &StatementKind::StorageDead(local) => Some(local.into()),
            _ => None,
        }
    }
}
impl<'tcx> AssignsToPlace<'tcx> for TerminatorKind<'tcx> {
    fn assigns_to(&self) -> Option<Place<'tcx>> {
        match self {
            TerminatorKind::Drop { place, .. }
            | TerminatorKind::Call {
                destination: place, ..
            }
            | TerminatorKind::Yield {
                resume_arg: place, ..
            } => Some(*place),
            _ => None,
        }
    }
}
