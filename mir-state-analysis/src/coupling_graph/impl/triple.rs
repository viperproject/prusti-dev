// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter, Result},
};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, OutlivesConstraint, RichLocation},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, ConstraintCategory, Local, Location, Operand,
            Place as MirPlace, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
            RETURN_PLACE,
        },
        ty::{RegionVid, TyKind},
    },
};

use crate::{
    coupling_graph::{region_info::map::RegionKind, region_place::PlaceRegion, CgContext},
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{Place, PlaceRepacker},
};

use super::{
    engine::{BorrowDelta, CoupligGraph},
    graph::{Graph, Node},
};

#[derive(Clone)]
pub struct Cg<'a, 'tcx> {
    pub id: Option<String>,
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub(crate) live: BitSet<BorrowIndex>,
    pub version: usize,
    pub dot_filter: fn(&RegionKind<'_>) -> bool,
    pub top_crates: bool,

    pub graph: Graph<'tcx>,
}

impl Debug for Cg<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Graph")
            .field("id", &self.id)
            .field("nodes", &self.graph)
            .finish()
    }
}

impl PartialEq for Cg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}
impl Eq for Cg<'_, '_> {}

impl<'a, 'tcx> DebugWithContext<CoupligGraph<'a, 'tcx>> for Cg<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CoupligGraph<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Cg<'a, 'tcx> {
    pub fn static_region(&self) -> RegionVid {
        self.cgx.region_info.static_region
    }
    pub fn function_region(&self) -> RegionVid {
        self.cgx.region_info.function_region
    }

    pub fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        let graph = Graph {
            nodes: IndexVec::from_elem_n(Node::new(), cgx.region_info.map.region_len()),
            static_regions: FxHashSet::from_iter([cgx.region_info.static_region]),
        };

        let live = BitSet::new_empty(cgx.facts2.borrow_set.location_map.len());
        Self {
            id: None,
            cgx,
            live,
            version: 0,
            dot_filter: |_| true,
            top_crates,
            graph,
        }
    }
    pub fn initialize_start_block(&mut self) {
        for c in &self.cgx.outlives_info.local_constraints {
            self.graph.outlives(*c);
        }
        for c in &self.cgx.outlives_info.universal_local_constraints {
            self.graph.outlives(*c);
        }
        for &(sup, sub) in &self.cgx.outlives_info.universal_constraints {
            self.graph.outlives_placeholder(sup, sub);
        }
    }

    #[tracing::instrument(name = "get_associated_place", level = "trace", skip(self), ret)]
    pub(crate) fn get_kind(&self, r: RegionVid) -> &RegionKind<'tcx> {
        self.cgx.region_info.map.get(r)
    }
    #[tracing::instrument(name = "is_unknown_local", level = "trace", skip(self), ret)]
    pub(crate) fn is_unknown_local(&self, r: RegionVid) -> bool {
        self.get_kind(r).is_unknown_local()
    }

    #[tracing::instrument(name = "handle_kills", level = "debug", skip(self))]
    pub fn handle_kills(
        &mut self,
        delta: &BorrowDelta,
        oos: Option<&Vec<BorrowIndex>>,
        location: Location,
    ) {
        let input_facts = self.cgx.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.cgx.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();

        for bi in delta.cleared.iter() {
            let data = &self.cgx.facts2.borrow_set[bi];
            // TODO: remove if the asserts below pass:
            let (r, _, l) = input_facts
                .loan_issued_at
                .iter()
                .find(|(_, b, _)| bi == *b)
                .copied()
                .unwrap();
            let l = rich_to_loc(location_table.to_location(l));
            assert_eq!(r, data.region);
            assert_eq!(l, data.reserve_location);

            // println!("killed: {r:?} {killed:?} {l:?}");
            if oos.map(|oos| oos.contains(&bi)).unwrap_or_default() {
                self.graph.kill_borrow(data);
            } else {
                self.graph.remove(data.region, Some(location));
            }

            // // TODO: is this necessary?
            // let local = data.borrowed_place.local;
            // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
            //     // println!("killed region: {region:?}");
            //     state.output_to_dot("log/coupling/kill.dot");
            //     let removed = state.remove(region, location, true, false);
            //     // assert!(!removed, "killed region: {region:?} at {location:?} (local: {local:?})");
            // }
        }

        if let Some(oos) = oos {
            for &bi in oos {
                // What is the difference between the two (oos)? It's that `delta.cleared` may kill it earlier than `oos`
                // imo we want to completely disregard `oos`. (TODO)
                // assert!(delta.cleared.contains(bi), "Cleared borrow not in out of scope: {:?} vs {:?} (@ {location:?})", delta.cleared, oos);
                if delta.cleared.contains(bi) {
                    continue;
                }

                let data = &self.cgx.facts2.borrow_set[bi];
                // TODO: remove if the asserts below pass:
                let (r, _, l) = input_facts
                    .loan_issued_at
                    .iter()
                    .find(|(_, b, _)| bi == *b)
                    .copied()
                    .unwrap();
                let l = rich_to_loc(location_table.to_location(l));
                assert_eq!(r, data.region);
                assert_eq!(l, data.reserve_location);

                self.graph.kill_borrow(data);

                // // TODO: is this necessary?
                // let local = data.assigned_place.local;
                // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                //     // println!("IHUBJ local: {local:?} region: {region:?}");
                //     let removed = state.remove(region, location, true, false);
                //     assert!(!removed);
                // }
            }
        }
    }

    #[tracing::instrument(name = "handle_outlives", level = "debug", skip(self))]
    pub fn handle_outlives(&mut self, location: Location, assigns_to: Option<MirPlace<'tcx>>) {
        let local = assigns_to.map(|a| a.local);
        for &c in self
            .cgx
            .outlives_info
            .pre_constraints(location, local, &self.cgx.region_info)
        {
            self.graph.outlives(c);
        }
        if let Some(place) = assigns_to {
            self.kill_shared_borrows_on_place(location, place);
        }
        for &c in self
            .cgx
            .outlives_info
            .post_constraints(location, local, &self.cgx.region_info)
        {
            self.graph.outlives(c);
        }
    }

    #[tracing::instrument(name = "kill_shared_borrows_on_place", level = "debug", skip(self))]
    pub fn kill_shared_borrows_on_place(&mut self, location: Location, place: MirPlace<'tcx>) {
        let Some(local) = place.as_local() else {
            // Only remove nodes if assigned to the entire local (this is what rustc allows too)
            return;
        };
        for region in self.cgx.region_info.map.all_regions() {
            if self.cgx.region_info.map.for_local(region, local) {
                self.graph.remove(region, Some(location));
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for Cg<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        match *operand {
            Operand::Copy(_) => (),
            Operand::Move(place) => {
                self.kill_shared_borrows_on_place(location, place);
            }
            Operand::Constant(..) => {
                // TODO: anything here?
            }
        }
    }
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Use(Operand::Constant(_)) => {
                // TODO: this is a hack, find a better way to do things
                for c in
                    self.cgx
                        .outlives_info
                        .pre_constraints(location, None, &self.cgx.region_info)
                {
                    self.graph
                        .outlives_static(c.sub, self.static_region(), location);
                }
            }
            _ => (),
        }
        self.super_rvalue(rvalue, location);
    }
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        match &statement.kind {
            StatementKind::AscribeUserType(box (p, _), _) => {
                for &c in self
                    .cgx
                    .outlives_info
                    .type_ascription_constraints
                    .iter()
                    .filter(|c| {
                        self.cgx.region_info.map.for_local(c.sup, p.local)
                            || self.cgx.region_info.map.for_local(c.sub, p.local)
                    })
                {
                    self.graph.outlives(c);
                }
            }
            _ => (),
        }
    }
}

impl<'tcx> Cg<'_, 'tcx> {
    #[tracing::instrument(name = "Regions::merge_for_return", level = "trace")]
    pub fn merge_for_return(&mut self, location: Location) {
        let regions: Vec<_> = self.graph.all_nodes().map(|(r, _)| r).collect();
        for r in regions {
            let kind = self.cgx.region_info.map.get(r);
            match kind {
                RegionKind::Static
                | RegionKind::Param(_)
                | RegionKind::UnknownUniversal
                | RegionKind::Function => continue,
                RegionKind::Place { local, .. } => {
                    if local.index() > self.cgx.rp.body().arg_count {
                        self.output_to_dot("log/coupling/error.dot", true);
                        panic!("{r:?} ({location:?}) {:?}", self.graph.nodes[r]);
                    }
                }
                RegionKind::Borrow(_) => {
                    // Should not have borrows left
                    self.output_to_dot("log/coupling/error.dot", true);
                    panic!("{r:?} {:?}", self.graph.nodes[r]);
                }
                // Ignore (and thus delete) early/late bound (mostly fn call) regions
                RegionKind::EarlyBound(..) => (),
                RegionKind::LateBound { .. } => (),
                RegionKind::Placeholder(..) => (),
                RegionKind::MiscLocal => (),
                // Skip unknown empty nodes, we may want to figure out how to deal with them in the future
                RegionKind::UnknownLocal => (),
            }
            self.graph.remove(r, None);
        }
    }
    pub fn output_to_dot<P: AsRef<std::path::Path>>(&self, path: P, error: bool) {
        if !self.top_crates || error {
            let mut f = std::fs::File::create(path).unwrap();
            dot::render(self, &mut f).unwrap();
        }
    }
}

fn rich_to_loc(l: RichLocation) -> Location {
    match l {
        RichLocation::Start(l) => l,
        RichLocation::Mid(l) => l,
    }
}
