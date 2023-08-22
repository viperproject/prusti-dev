// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::RefCell;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxIndexMap},
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{Borrows, BorrowIndex, RichLocation, calculate_borrows_out_of_scope_at_location},
    },
    dataflow::{Analysis, AnalysisDomain, CallReturnPlaces, ResultsCursor},
    index::{bit_set::{BitSet, HybridBitSet}, Idx},
    middle::{
        mir::{
            TerminatorKind, Operand, ConstantKind, StatementKind, Rvalue,
            visit::Visitor, BasicBlock, Body, Local, Location, Statement, Terminator, RETURN_PLACE,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, Fpcs},
    utils::PlaceRepacker, coupling_graph::cg::{Graph, Node},
};

use super::cg::{Cg, Regions};

pub(crate) struct CoupligGraph<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) facts: &'a BorrowckFacts,
    pub(crate) facts2: &'a BorrowckFacts2<'tcx>,
    pub(crate) flow_borrows: RefCell<ResultsCursor<'a, 'tcx, Borrows<'a, 'tcx>>>,
    pub(crate) out_of_scope: FxIndexMap<Location, Vec<BorrowIndex>>,
}
impl<'a, 'tcx> CoupligGraph<'a, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, facts: &'a BorrowckFacts, facts2: &'a BorrowckFacts2<'tcx>) -> Self {
        std::fs::remove_dir_all("log/coupling").ok();
        std::fs::create_dir_all("log/coupling").unwrap();

        let repacker = PlaceRepacker::new(body, tcx);
        let regioncx = &*facts2.region_inference_context;
        let borrow_set = &*facts2.borrow_set;
        let out_of_scope = calculate_borrows_out_of_scope_at_location(body, regioncx, borrow_set);
        let flow_borrows = Borrows::new(tcx, body, regioncx, borrow_set)
            .into_engine(tcx, body)
            .pass_name("borrowck")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        CoupligGraph { repacker, facts, facts2, flow_borrows: RefCell::new(flow_borrows), out_of_scope }
    }

    fn handle_diff(&self, state: &mut Regions<'_, 'tcx>, delta: BorrowDelta, location: Location) {
        let input_facts = self.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();
        for idx in delta.set.iter() {
            let loan_issued_at = &input_facts.loan_issued_at;
            let (r, _, l) = loan_issued_at.iter().find(|(_, b, _)| idx == *b).copied().unwrap();
            let l = location_table.to_location(l);
            let RichLocation::Mid(l) = l else { unreachable!() };
            assert_eq!(l, location);
            let locals = input_facts.use_of_var_derefs_origin.iter().filter(|(_, ro)| r == *ro).map(|(l, _)| (*l, r)).collect::<Vec<_>>();
            state.borrows.insert(idx, (vec![r], locals));
        }
        state.subset.extend(input_facts.subset_base.iter().filter(
            |(_, _, l)| rich_to_loc(location_table.to_location(*l)) == location
        ).map(|(r1, r2, _)| (*r1, *r2)));
        // TODO: do a proper fixpoint here
        for _ in 0..10 {
            for &(r1, r2) in &state.subset {
                let locals = input_facts.use_of_var_derefs_origin.iter().filter(|(_, ro)| r2 == *ro).map(|(l, _)| (*l, r2)).collect::<Vec<_>>();
                let mut did_push = false;
                for (_, s) in state.borrows.iter_mut() {
                    if s.0.contains(&r1) {
                        did_push = true;
                        if !s.0.contains(&r2) {
                            s.0.push(r2);
                            s.1.extend(locals.iter().copied());
                        }
                    }
                }
                // assert!(did_push, "r1: {:?}, r2: {:?}, location: {:?}, state: {:?}", r1, r2, location, state);
            }
        }
        for r in delta.cleared.iter() {
            let removed = state.borrows.remove(&r).unwrap();
            // for (_, s) in state.borrows.iter_mut() {
            //     s.0.retain(|r| !removed.0.contains(r));
            //     s.1.retain(|l| !removed.1.contains(l));
            // }
        }
        // print!(" {:?}", state.borrows);
        self.handle_graph(state, delta, location);
    }

    fn handle_graph(&self, state: &mut Regions<'_, 'tcx>, delta: BorrowDelta, location: Location) {
        let l = format!("{:?}", location).replace('[', "_").replace(']', "");

        let input_facts = self.facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let location_table = self.facts.location_table.borrow();
        let location_table = location_table.as_ref().unwrap();

        // let input_facts = self.facts2.region_inference_context.borrow();

        let oos = self.out_of_scope.get(&location);
        if let Some(oos) = oos {
            for bi in oos {
                let (r, _, l) = input_facts.loan_issued_at.iter().find(
                    |(_, b, _)| bi == b
                ).copied().unwrap();
                println!("UGHBJS region: {r:?} location: {l:?}");
                state.graph.kill(r);
                let l = rich_to_loc(location_table.to_location(l));
                let borrow_data = self.facts2.borrow_set.location_map.get(&l).unwrap();
                let local = borrow_data.assigned_place.local;
                for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                    println!("IHUBJ local: {local:?} region: {region:?}");
                    state.graph.remove(region, true);
                }
            }
        }

        // let mut f = std::fs::File::create(format!("log/coupling/{l}_a.dot")).unwrap();
        // dot::render(&state.graph, &mut f).unwrap();

        for killed in delta.cleared.iter() {
            if oos.map(|oos| oos.contains(&killed)).unwrap_or_default() {
                continue;
            }
            let (r, _, l) = input_facts.loan_issued_at.iter().find(
                |(_, b, _)| killed == *b
            ).copied().unwrap();
            state.graph.remove(r, false);
            let l = rich_to_loc(location_table.to_location(l));
            let borrow_data = self.facts2.borrow_set.location_map.get(&l).unwrap();
            let local = borrow_data.borrowed_place.local;
            for region in input_facts.use_of_var_derefs_origin.iter().filter(|(l, _)| *l == local).map(|(_, r)| *r) {
                state.graph.remove(region, true);
            }
        }

        // let mut f = std::fs::File::create(format!("log/coupling/{l}_b.dot")).unwrap();
        // dot::render(&state.graph, &mut f).unwrap();

        // let new_subsets: Vec<_> = input_facts.subset_base.iter().filter(
        //     |(_, _, l)| rich_to_loc(location_table.to_location(*l)) == location
        // ).map(|(r1, r2, _)| (*r1, *r2)).collect();
        // for (r1, r2) in new_subsets {
        //     state.graph.outlives(r1, r2);
        // }
        let constraints = self.facts2.region_inference_context.outlives_constraints();
        for c in constraints {
            if let Some(from) = c.locations.from_location() {
                if from == location {
                    state.graph.outlives(c.sup, c.sub, c.category);
                }
            }
        }

        if !self.repacker.body().basic_blocks[location.block].is_cleanup {
            let mut f = std::fs::File::create(format!("log/coupling/{l}_c.dot")).unwrap();
            dot::render(&state.graph, &mut f).unwrap();
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for CoupligGraph<'a, 'tcx> {
    type Domain = Cg<'a, 'tcx>;
    const NAME: &'static str = "coupling_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Cg::new(self.repacker, self.facts, self.facts2)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        // println!("body: {body:?}");
        println!("\ninput_facts: {:?}", self.facts.input_facts);
        println!("output_facts: {:#?}\n", self.facts.output_facts);
        println!("location_map: {:#?}\n", self.facts2.borrow_set.location_map);
        println!("activation_map: {:#?}\n", self.facts2.borrow_set.activation_map);
        println!("local_map: {:#?}\n", self.facts2.borrow_set.local_map);
        // println!("region_inference_context: {:#?}\n", self.facts2.region_inference_context);
        // println!("locals_state_at_exit: {:#?}\n", self.facts2.borrow_set.locals_state_at_exit);
        let lt = self.facts.location_table.borrow();
        let lt = lt.as_ref().unwrap();
        for pt in lt.all_points() {
            println!("{pt:?} -> {:?} ({:?})", lt.to_location(pt), ""); //, self.facts.output_facts.origins_live_at(pt));
        }
        println!("out_of_scope: {:?}", self.out_of_scope);
    }
}

impl<'a, 'tcx> Analysis<'tcx> for CoupligGraph<'a, 'tcx> {
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        if location.statement_index == 0 {
            println!("\nblock: {:?}", location.block);
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        // print!("{statement:?} ({other:?}):");
        let delta = calculate_diff(&other, &state.live);
        if delta.set.is_empty() {
            match statement.kind {
                StatementKind::Assign(box (assigned_place, Rvalue::Ref(region, kind, borrowed_place))) => {

                    state.regions.graph.new_shared_borrow(BorrowData {
                        reserve_location: location,
                        activation_location: TwoPhaseActivation::NotTwoPhase,
                        kind,
                        region: region.as_var(),
                        borrowed_place,
                        assigned_place,
                    })
                }
                _ => (),
            }
        }
        self.handle_diff(&mut state.regions, delta, location);
        state.live = other;
        // println!();
    }

    fn apply_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        if location.statement_index == 0 {
            println!("\nblock: {:?}", location.block);
            self.flow_borrows.borrow_mut().seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows.borrow_mut().seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        if let TerminatorKind::Call { func, args, destination, target, fn_span, .. } = &terminator.kind {
            if let Operand::Constant(c) = func {
                println!("user_ty: {:?}", c.user_ty);
                println!("call: {:?}", c.literal);
                if let ConstantKind::Val(cv, ty) = c.literal {
                    println!("val: {:?}", cv);
                    println!("ty: {:?}", ty);
                }
                println!("\n\n\ncall: {:?}", func);
            }
            for arg in args {
                match arg {
                    Operand::Copy(a) => println!("copy ({arg:?}): {:?}", a),
                    Operand::Move(b) => println!("move ({arg:?}): {:?}", b),
                    Operand::Constant(c) => println!("const ({arg:?}): {:?}", c.literal),
                }
            }
        }
        // print!("{terminator:?} ({other:?}):");
        let delta = calculate_diff(&other, &state.live);
        self.handle_diff(&mut state.regions, delta, location);
        state.live = other;
        // println!();
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}

struct BorrowDelta {
    set: HybridBitSet<BorrowIndex>,
    cleared: HybridBitSet<BorrowIndex>,
}

fn calculate_diff(curr: &BitSet<BorrowIndex>, old: &BitSet<BorrowIndex>) -> BorrowDelta {
    let size = curr.domain_size();
    assert_eq!(size, old.domain_size());

    let mut set_in_curr = HybridBitSet::new_empty(size);
    let mut cleared_in_curr = HybridBitSet::new_empty(size);

    for i in (0..size).map(BorrowIndex::new) {
        match (curr.contains(i), old.contains(i)) {
            (true, false) => set_in_curr.insert(i),
            (false, true) => cleared_in_curr.insert(i),
            _ => continue,
        };
    }
    BorrowDelta {
        set: set_in_curr,
        cleared: cleared_in_curr,
    }
}

fn rich_to_loc(l: RichLocation) -> Location {
    match l {
        RichLocation::Start(l) => l,
        RichLocation::Mid(l) => l,
    }
}
