// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter, Result}, rc::Rc,
};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{BorrowIndex, OutlivesConstraint, RichLocation, PlaceConflictBias, places_conflict},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{
            interpret::{ConstValue, GlobalAlloc, Scalar},
            visit::Visitor,
            BasicBlock, BorrowKind, ConstantKind, ConstraintCategory, Local, Location, Operand,
            Place as MirPlace, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
            RETURN_PLACE,
        },
        ty::{GenericArgKind, ParamEnv, RegionVid, TyKind},
    },
};

use crate::{
    coupling_graph::{
        coupling::{Block, CouplingOp},
        outlives_info::edge::{EdgeInfo, EdgeOrigin},
        region_info::map::{Promote, RegionKind},
        CgContext,
    },
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections,
        RepackOp,
    },
    utils::{r#const::ConstEval, Place, PlaceRepacker},
};

use super::{
    engine::{BorrowDelta, CgEngine},
    graph::{Graph, Node},
};

#[derive(Clone)]
pub struct CouplingGraph<'a, 'tcx> {
    pub location: Location,
    pub is_pre: bool,
    pub cgx: Rc<CgContext<'a, 'tcx>>,

    pub version: FxHashMap<BasicBlock, usize>,
    pub dot_node_filter: fn(&RegionKind<'_>) -> bool,
    pub dot_edge_filter: fn(&RegionKind<'_>, &RegionKind<'_>) -> bool,
    pub top_crates: bool,

    pub start: Graph<'tcx>,
    pub after: Graph<'tcx>,

    // TODO: remove
    pub couplings: Vec<CouplingOp>,
    pub touched: FxHashSet<RegionVid>,
}

impl Debug for CouplingGraph<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Graph")
            .field("location", &self.location)
            .field("version", &self.version)
            // .field("nodes", &self.graph)
            .finish()
    }
}

impl PartialEq for CouplingGraph<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.after == other.after
    }
}
impl Eq for CouplingGraph<'_, '_> {}

impl<'a, 'tcx> DebugWithContext<CgEngine<'a, 'tcx>> for CouplingGraph<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CgEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        for op in &self.couplings {
            writeln!(f, "{op}")?;
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a> CouplingGraph<'a, 'tcx> {
    pub fn static_region(&self) -> RegionVid {
        self.cgx.region_info.static_region
    }
    pub fn function_region(&self) -> RegionVid {
        self.cgx.region_info.function_region
    }

    #[tracing::instrument(name = "CouplingGraph::new", level = "trace", skip_all)]
    pub fn new(cgx: Rc<CgContext<'a, 'tcx>>, top_crates: bool, block: BasicBlock) -> Self {
        let after = Graph {
            nodes: IndexVec::from_elem_n(Node::new(), cgx.region_info.map.region_len()),
            static_regions: FxHashSet::from_iter([cgx.region_info.static_region]),
            inactive_loans: FxHashSet::default(),
        };

        Self {
            location: Location { block, statement_index: 0 },
            is_pre: true,
            cgx,
            version: FxHashMap::default(),
            dot_node_filter: |_| true,
            dot_edge_filter: |_, _| true,
            top_crates,
            start: Graph::empty(),
            after,
            couplings: Vec::new(),
            touched: FxHashSet::default(),
        }
    }
    pub fn initialize_start_block(&mut self, cgx: &CgContext<'a, 'tcx>) {
        for c in &cgx.outlives_info.local_constraints {
            self.outlives(*c);
        }
        for c in &cgx.outlives_info.universal_local_constraints {
            self.outlives(*c);
        }
        for &(sup, sub) in &cgx.outlives_info.universal_constraints {
            self.outlives_placeholder(sup, sub, EdgeOrigin::RustcUniversal);
        }
        for &const_region in cgx.region_info.map.const_regions() {
            self.outlives_static(const_region, EdgeOrigin::Static);
        }
        // Remove all locals without capabilities from the initial graph
        self.kill_regions_on_place(None, RETURN_PLACE.into());
        for local in self.cgx.rp.body().vars_and_temps_iter() {
            self.kill_regions_on_place(None, local.into());
        }
    }
    pub fn sum_version(&self) -> usize {
        self.version.values().copied().sum::<usize>()
    }

    pub(crate) fn outlives(&mut self, c: OutlivesConstraint<'tcx>) {
        let edge = EdgeInfo::from(c).to_edge(&self.cgx);
        let new = self.after.outlives(edge);
        self.outlives_op(new)
    }
    pub(crate) fn outlives_static(&mut self, r: RegionVid, origin: EdgeOrigin) {
        let static_region = self.static_region();
        if r == static_region {
            return;
        }
        self.outlives_placeholder(r, static_region, origin)
    }
    pub(crate) fn outlives_placeholder(
        &mut self,
        r: RegionVid,
        placeholder: RegionVid,
        origin: EdgeOrigin,
    ) {
        let edge = EdgeInfo::no_reason(r, placeholder, None, origin).to_edge(&self.cgx);
        // let new = self.graph.outlives_placeholder(r, placeholder, origin);
        let new = self.after.outlives(edge);
        self.outlives_op(new)
    }
    #[tracing::instrument(name = "CouplingGraph::outlives_op", level = "trace", skip(self))]
    fn outlives_op(&mut self, op: Option<(RegionVid, RegionVid, bool)>) {
        if let Some(block) = op.and_then(|c| self.outlives_to_block(c)) {
            self.couplings.push(CouplingOp::Add(block));
        }
    }

    // TODO: remove
    pub(crate) fn outlives_to_block(&self, op: (RegionVid, RegionVid, bool)) -> Option<Block> {
        let (sup, sub, is_blocking) = op;
        if is_blocking {
            let waiting_to_activate = self.after.inactive_loans.contains(&sup);
            Some(Block {
                sup,
                sub,
                waiting_to_activate,
            })
        } else {
            None
        }
    }
    #[tracing::instrument(name = "CouplingGraph::remove", level = "debug", skip(self))]
    pub(crate) fn remove(&mut self, r: RegionVid, l: Option<Location>) {
        let remove = self.after.remove(r);
        if let Some(op) = remove {
            self.remove_op(op);
        }
    }
    #[tracing::instrument(name = "CouplingGraph::outlives_op", level = "trace", skip(self))]
    fn remove_op(&mut self, op: (RegionVid, Vec<(RegionVid, RegionVid, bool)>)) {
        let rejoins =
            op.1.into_iter()
                .flat_map(|c| self.outlives_to_block(c))
                .collect();
        self.couplings.push(CouplingOp::Remove(op.0, rejoins));
    }
    #[tracing::instrument(name = "CouplingGraph::remove", level = "debug", skip(self), ret)]
    pub(crate) fn remove_many(&mut self, mut r: FxHashSet<RegionVid>) {
        let ops = self.after.remove_many(&r);
        for op in ops {
            r.remove(&op.0);
            self.remove_op(op);
        }
        for removed in r {
            self.couplings.push(CouplingOp::Remove(removed, Vec::new()));
        }
        // let rejoins = rejoins.into_iter().flat_map(|c| self.outlives_to_block(c)).collect();
        // self.couplings.push(CouplingOp::RemoveMany(removed, rejoins));
    }
    #[tracing::instrument(name = "CouplingGraph::kill_borrow", level = "trace", skip(self))]
    pub(crate) fn kill_borrow(&mut self, data: &BorrowData<'tcx>) {
        let remove = self.after.kill_borrow(data);
        for removed in remove.into_iter().rev() {
            self.couplings.push(CouplingOp::Remove(removed, Vec::new()));
        }
    }
    pub(crate) fn reset_ops(&mut self) {
        for c in self.couplings.drain(..) {
            self.touched.extend(c.regions());
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
        oos: &[BorrowIndex],
        location: Location,
        assigned_to: Option<MirPlace<'tcx>>,
    ) {
        for &bi in oos {
            let data = &self.cgx.mir.borrow_set[bi];
            self.kill_borrow(data);

            // // TODO: is this necessary?
            // let local = data.assigned_place.local;
            // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
            //     // println!("IHUBJ local: {local:?} region: {region:?}");
            //     let removed = state.remove(region, location, true, false);
            //     assert!(!removed);
            // }
        }

        if let Some(borrow) = self.cgx.mir.borrow_set.location_map.get(&location) {
            if let TwoPhaseActivation::ActivatedAt(_) = borrow.activation_location {
                self.after.inactive_loans.insert(borrow.region);
            }
        }
        for activated in self.cgx.activations_at_location(location) {
            let borrow = &self.cgx.mir.borrow_set[*activated];
            let contained = self.after.inactive_loans.remove(&borrow.region);
            assert!(contained);
            self.couplings.push(CouplingOp::Activate(borrow.region));
        }

        if let Some(place) = assigned_to {
            self.kill_regions_on_place(Some(location), place);
        }
    }

    #[tracing::instrument(name = "handle_outlives", level = "debug", skip(self))]
    pub fn handle_outlives(&mut self, location: Location, assigns_to: Option<MirPlace<'tcx>>) {
        let local = assigns_to.map(|a| a.local);
        for c in self
            .cgx
            .outlives_info
            .pre_constraints(location, local, &self.cgx.region_info)
            .cloned()
            .collect::<Vec<_>>()
        {
            self.outlives(c);
        }
        // if let Some(place) = assigns_to {
        //     self.kill_regions_on_place(Some(location), place);
        // }
        for c in self
            .cgx
            .outlives_info
            .post_constraints(location, local, &self.cgx.region_info)
            .cloned()
            .collect::<Vec<_>>()
        {
            self.outlives(c);
        }
    }

    #[tracing::instrument(name = "kill_regions_on_place", level = "debug", skip(self))]
    pub fn kill_regions_on_place(
        &mut self,
        location: Option<Location>,
        place: MirPlace<'tcx>,
    ) {
        if let Some(local) = place.as_local() {
            for region in self.cgx.region_info.map.all_regions() {
                if self.cgx.region_info.map.for_local(region, local) {
                    self.remove(region, location);
                }
            }
        } else {
            for region in self.cgx.region_info.map.all_regions() {
                if let Some(bw) = self.cgx.region_info.map.get(region).get_borrow() {
                    if places_conflict(
                        self.cgx.rp.tcx(),
                        &self.cgx.mir.body,
                        bw.borrowed_place,
                        place,
                        PlaceConflictBias::NoOverlap,
                    ) {
                        self.remove(region, location);
                    }
                }
            }
        };
    }
}

impl<'tcx> Visitor<'tcx> for CouplingGraph<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        match operand {
            Operand::Copy(_) => (),
            &Operand::Move(place) => {
                self.kill_regions_on_place(Some(location), place);
            }
            Operand::Constant(_) => (),
        }
    }
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        match &statement.kind {
            StatementKind::AscribeUserType(box (p, _), _) => {
                for c in self
                    .cgx
                    .outlives_info
                    .type_ascription_constraints
                    .iter()
                    .filter(|c| {
                        self.cgx.region_info.map.for_local(c.sup, p.local)
                            || self.cgx.region_info.map.for_local(c.sub, p.local)
                    })
                    .cloned()
                    .collect::<Vec<_>>()
                {
                    self.outlives(c);
                }
            }
            _ => (),
        }
    }
}

impl<'tcx> CouplingGraph<'_, 'tcx> {
    #[tracing::instrument(name = "CouplingGraph::merge_for_return", level = "debug")]
    pub fn merge_for_return(&mut self, location: Location) {
        let regions: Vec<_> = self.after.all_nodes().map(|(r, _)| r).collect();
        let mut to_remove = FxHashSet::default();
        for r in regions {
            let kind = self.cgx.region_info.map.get(r);
            match kind {
                RegionKind::Static
                | RegionKind::Param(_)
                | RegionKind::UnknownUniversal
                | RegionKind::Function => continue,
                RegionKind::Place {
                    local,
                    promoted: Promote::NotPromoted,
                    ..
                } => {
                    if local.index() > self.cgx.rp.body().arg_count {
                        self.output_to_dot("log/coupling/error.dot", true);
                        panic!("{r:?} ({location:?}) {:?}", self.after.nodes[r]);
                    }
                }
                RegionKind::Borrow(_, Promote::NotPromoted) => {
                    // Should not have borrows left
                    self.output_to_dot("log/coupling/error.dot", true);
                    panic!("{r:?} {:?}", self.after.nodes[r]);
                }
                // Ignore (and thus delete) early/late bound (mostly fn call) regions
                RegionKind::UnusedReturnBug(..) => unreachable!(),
                RegionKind::Place {
                    promoted: Promote::Promoted(..),
                    ..
                } => (),
                RegionKind::Borrow(_, Promote::Promoted(..)) => (),
                RegionKind::ConstRef(..) => (),
                RegionKind::EarlyBound(..) => (),
                RegionKind::LateBound { .. } => (),
                RegionKind::Placeholder(..) => (),
                RegionKind::MiscLocal => (),
                RegionKind::ProjectionAnnotation(..) => (),
                RegionKind::OtherAnnotation(..) => (),
                // Skip unknown empty nodes, we may want to figure out how to deal with them in the future
                RegionKind::UnknownLocal => (),
            }
            to_remove.insert(r);
        }
        self.remove_many(to_remove);
    }
    #[tracing::instrument(name = "CouplingGraph::output_to_dot", level = "debug", skip_all)]
    pub fn output_to_dot<P: AsRef<std::path::Path>>(&self, path: P, error: bool) {
        if cfg!(debug_assertions) && (!self.top_crates || error) {
            std::fs::create_dir_all("log/coupling/individual").unwrap();
            let mut f = std::fs::File::create(path).unwrap();
            dot::render(self, &mut f).unwrap();
        }
    }
}




// let input_facts = self.cgx.mir.input_facts.as_ref().unwrap();
// let location_table = self.cgx.mir.location_table.as_ref().unwrap();

// for bi in delta.cleared.iter() {
//     let data = &self.cgx.mir.borrow_set[bi];
//     // println!("killed: {r:?} {killed:?} {l:?}");
//     if oos.map(|oos| oos.contains(&bi)).unwrap_or_default() {
//         if self.graph.static_regions.contains(&data.region) {
//             self.output_to_dot("log/coupling/kill.dot", true);
//         }
//         assert!(
//             !self.graph.static_regions.contains(&data.region),
//             "{data:?} {location:?} {:?}",
//             self.graph.static_regions
//         );
//         self.kill_borrow(data);
//     } else {
//         self.remove(data.region, Some(location));
//     }

//     // // TODO: is this necessary?
//     // let local = data.borrowed_place.local;
//     // for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
//     //     // println!("killed region: {region:?}");
//     //     state.output_to_dot("log/coupling/kill.dot");
//     //     let removed = state.remove(region, location, true, false);
//     //     // assert!(!removed, "killed region: {region:?} at {location:?} (local: {local:?})");
//     // }
// }
//     // What is the difference between the two (oos)? It's that `delta.cleared` may kill it earlier than `oos`
//     // imo we want to completely disregard `oos`. (TODO)
//     // assert!(delta.cleared.contains(bi), "Cleared borrow not in out of scope: {:?} vs {:?} (@ {location:?})", delta.cleared, oos);
//     if delta.cleared.contains(bi) {
//         continue;
//     }