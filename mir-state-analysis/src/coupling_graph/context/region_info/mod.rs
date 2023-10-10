// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, Borrows, OutlivesConstraint, PoloniusInput, RustcFacts},
    },
    data_structures::fx::FxHashMap,
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{visit::Visitor, Body, Constant, Local, Location, Operand, RETURN_PLACE, Rvalue, ConstantKind},
        ty::{GenericArg, RegionVid, Ty, TyCtxt},
    },
};

use crate::{
    coupling_graph::region_info::map::ParamRegion,
    utils::{Place, PlaceRepacker, r#const::ConstEval},
};

use self::map::{RegionInfoMap, RegionKind};

use super::{region_place::PlaceRegion, shared_borrow_set::SharedBorrowSet};

pub mod map;

#[derive(Debug)]
pub struct RegionInfo<'tcx> {
    pub map: RegionInfoMap<'tcx>,
    pub static_region: RegionVid,
    pub function_region: RegionVid,
}

impl<'tcx> RegionInfo<'tcx> {
    pub fn new(
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2<'tcx>,
        sbs: &SharedBorrowSet<'tcx>,
    ) -> Self {
        let mut map = RegionInfoMap::new(
            input_facts.universal_region.len(),
            facts2.region_inference_context.var_infos.len(),
        );
        // Assumption: universal regions are the first regions
        debug_assert!(input_facts
            .universal_region
            .iter()
            .all(|&r| map.is_universal(r)));

        // Init universals
        let (static_region, function_region) =
            Self::initialize_universals(&mut map, rp, input_facts, facts2);

        // Init consts
        Self::initialize_consts(&mut map, rp);

        // Init locals
        Self::initialize_locals(&mut map, rp, input_facts, facts2, sbs);

        // Init from `var_infos`
        for r in map.all_regions() {
            let info = facts2.region_inference_context.var_infos[r];
            map.set_region_info(r, info);
        }

        Self {
            map,
            static_region,
            function_region,
        }
    }

    pub fn initialize_universals(
        map: &mut RegionInfoMap<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2,
    ) -> (RegionVid, RegionVid) {
        let static_region = *input_facts.universal_region.first().unwrap();
        // Check that static is actually first
        if cfg!(debug_symbols) {
            // Static should outlive all other placeholders
            let outlives = input_facts
                .known_placeholder_subset
                .iter()
                .filter(|&&(sup, sub)| {
                    assert_ne!(static_region, sub);
                    static_region == sup
                });
            assert_eq!(outlives.count(), map.universal() - 1);
        }
        let function_region = *input_facts.universal_region.last().unwrap();
        // Check that the function region is actually last
        if cfg!(debug_symbols) {
            // All other placeholders should outlive the function region
            let outlives = input_facts
                .known_placeholder_subset
                .iter()
                .filter(|&&(sup, sub)| {
                    assert_ne!(function_region, sup);
                    function_region == sub
                });
            assert_eq!(outlives.count(), map.universal() - 1);
        }

        // Collect equivalences between universal and local
        let mut equivalence_map: FxHashMap<(RegionVid, RegionVid), u8> = FxHashMap::default();
        for c in facts2
            .region_inference_context
            .outlives_constraints()
            .filter(|o| {
                o.locations.from_location().is_none()
                    && (map.is_universal(o.sup) || map.is_universal(o.sub))
                    && !(map.is_universal(o.sup) && map.is_universal(o.sub))
            })
        {
            let (universal, other, incr) = if map.is_universal(c.sup) {
                (c.sup, c.sub, 1)
            } else {
                (c.sub, c.sup, 2)
            };
            let entry = equivalence_map.entry((universal, other)).or_default();
            *entry |= incr;
            // Note: Outlives constraints may be duplicated!!
            // e.g. in `hashbrown-0.14.1` in `hashbrown::raw::RawTable::<T, A>::clear::{closure#0}` at `src/raw/mod.rs:1021:37: 1021:66 (#0)`
        }

        // Set the entries in the map
        map.set(static_region, RegionKind::Static);
        for ((universal, local), sum) in equivalence_map {
            if sum == 3 {
                map.set_param(universal, local);
            }
        }
        map.set(function_region, RegionKind::Function);
        (static_region, function_region)
    }

    pub fn initialize_consts(map: &mut RegionInfoMap<'tcx>, rp: PlaceRepacker<'_, 'tcx>) {
        let mut collector = ConstantRegionCollector { map };
        collector.visit_body(rp.body());
        for constant in &rp.body().required_consts {
            for r in constant.ty().walk().flat_map(|ga| ga.as_region()) {
                assert!(r.is_var(), "{r:?} in {constant:?}");
                map.set(r.as_var(), RegionKind::ConstRef(true));
            }
        }
    }

    pub fn initialize_locals(
        map: &mut RegionInfoMap<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
        input_facts: &PoloniusInput,
        facts2: &BorrowckFacts2<'tcx>,
        sbs: &SharedBorrowSet<'tcx>,
    ) {
        for &(local, region) in &input_facts.use_of_var_derefs_origin {
            map.set(region, RegionKind::Place { region, local });
        }
        for data in sbs
            .location_map
            .values()
            .chain(facts2.borrow_set.location_map.values())
        {
            map.set(data.region, RegionKind::Borrow(data.clone()));
        }
    }
}

struct ConstantRegionCollector<'a, 'tcx> {
    map: &'a mut RegionInfoMap<'tcx>,
}
impl<'tcx> Visitor<'tcx> for ConstantRegionCollector<'_, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        // We might have a non-var `r` as the function operand (const) to a function call.
        // This function call may be e.g. `ParseBuffer::<'_>::step` and we want to ignore the `'_`.
        // So instead of matching on arbitrary constants, we only match on Rvalue creation of them.
        self.super_rvalue(rvalue, location);
        if let Rvalue::Use(Operand::Constant(constant)) = rvalue {
            for r in constant.ty().walk().flat_map(|ga| ga.as_region()) {
                // We may run into non-var regions here, e.g. assigning a const closure to a local where
                // the closure captures state and thus that has e.g. `BrNamed` regions.
                if  r.is_var() {
                    // assert!(r.is_var(), "{r:?} in {constant:?} ({:?} at {location:?})", constant.ty());
                    self.map.set(r.as_var(), RegionKind::ConstRef(false));
                }
            }
        }
    }
}
