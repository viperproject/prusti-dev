// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::loops;
use crate::data::ProcedureDefId;
use prusti_rustc_interface::middle::mir::{self, Body as Mir, Rvalue, AggregateKind};
use prusti_rustc_interface::middle::mir::{BasicBlock, BasicBlockData};
use prusti_rustc_interface::middle::ty::{Ty, TyCtxt};
use std::rc::Rc;
use std::collections::{HashSet, HashMap};
use prusti_rustc_interface::span::Span;
use log::{trace, debug};
use prusti_rustc_interface::middle::mir::StatementKind;
use prusti_rustc_interface::hir::def_id;
use crate::environment::mir_utils::RealEdges;
use crate::environment::debug_utils::to_text::ToText;
use crate::environment::Environment;

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'tcx> {
    tcx: TyCtxt<'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Rc<Mir<'tcx>>,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
    reachable_basic_blocks: HashSet<BasicBlock>,
    nonspec_basic_blocks: HashSet<BasicBlock>,
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub fn new(env: &Environment<'tcx>, proc_def_id: ProcedureDefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let tcx = env.tcx();
        // TOOD(tymap): add substs to procedure? check usages
        let mir = env.local_mir(proc_def_id.expect_local(), env.identity_substs(proc_def_id));
        let real_edges = RealEdges::new(&mir);
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir, &real_edges);
        let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir, &real_edges, &tcx);
        let loop_info = loops::ProcedureLoops::new(&mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            mir,
            real_edges,
            loop_info,
            reachable_basic_blocks,
            nonspec_basic_blocks,
        }
    }

    pub fn loop_info(&self) -> &loops::ProcedureLoops {
        &self.loop_info
    }

    /// Returns all the types used in the procedure, and any types reachable from them
    pub fn get_declared_types(&self) -> Vec<Ty<'tcx>> {
        let _types: HashSet<Ty> = HashSet::new();
        // for var in &self.mir.local_decls {
        //     for ty in var.ty.walk() {
        //         let declared_ty = ty;
        //         //let declared_ty = clean_type(tcx, ty);
        //         //let declared_ty = tcx.erase_regions(&ty);
        //         types.insert(declared_ty);
        //     }
        // }
        // types.into_iter().collect()
        unimplemented!();

    }

    pub fn get_lifetime_of_var(&self, var: mir::Local) -> Option<String>{
        fn get_lifetime_if_matches(local: mir::Local, var: mir::Local, mir: &Mir) -> Option<String>{
            if local == var {
                let ty_kind = mir.local_decls[local].ty.kind();
                if let prusti_rustc_interface::middle::ty::TyKind::Ref(region, _ty, _mutability) = ty_kind {
                    return Some(region.to_text());
                }
            }
            None
        }
        let mir = self.get_mir();
        for local in mir.vars_and_temps_iter() {
            if let Some(lifetime) = get_lifetime_if_matches(local, var, mir) {
                return Some(lifetime);
            }
        }
        for local in mir.args_iter() {
            if let Some(lifetime) = get_lifetime_if_matches(local, var, mir) {
                return Some(lifetime);
            }
        }
        None
    }

    pub fn get_var_of_lifetime(&self, lft: &str) -> Option<mir::Local>{
        let mir = self.get_mir();
        for local in mir.vars_and_temps_iter() {
            if let prusti_rustc_interface::middle::ty::TyKind::Ref(region, _, _) = &mir.local_decls[local].ty.kind() {
                if region.to_text() == lft {
                    return Some(local)
                }
            }
        }
        None
    }

    /// Get definition ID of the procedure.
    pub fn get_id(&self) -> ProcedureDefId {
        self.proc_def_id
    }

    /// Get the MIR of the procedure
    pub fn get_mir(&self) -> &Mir<'tcx> {
        &self.mir
    }

    /// Get the typing context.
    pub fn get_tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_def_path(&self) -> String {
        let def_path = self.tcx.def_path(self.proc_def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    // /// Get a short name of the procedure
    // pub fn get_short_name(&self) -> String {
    //     self.tcx.item_path_str(self.proc_def_id)
    // }

    // /// Get a readable path of the procedure
    // pub fn get_name(&self) -> String {
    //     self.tcx.absolute_item_path_str(self.proc_def_id)
    // }

    /// Get the span of the procedure
    pub fn get_span(&self) -> Span {
        self.mir.span
    }

    /// Get the first CFG block
    pub fn get_first_cfg_block(&self) -> BasicBlock {
        self.mir.basic_blocks().indices().next().unwrap()
    }

    /// Iterate over all CFG basic blocks
    pub fn get_all_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.loop_info.ordered_blocks.clone()
    }

    /// Iterate over all reachable CFG basic blocks
    pub fn get_reachable_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.get_all_cfg_blocks()
            .into_iter()
            .filter(|bbi| self.is_reachable_block(*bbi))
            .collect()
    }

    /// Iterate over all reachable CFG basic blocks that are not part of the specification type checking
    pub fn get_reachable_nonspec_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.get_reachable_cfg_blocks()
            .into_iter()
            .filter(|bbi| !self.is_spec_block(*bbi))
            .collect()
    }

    /// Check whether the block is used for typechecking the specification
    pub fn is_spec_block(&self, bbi: BasicBlockIndex) -> bool {
        !self.nonspec_basic_blocks.contains(&bbi)
    }

    /// Check whether the block is reachable
    pub fn is_reachable_block(&self, bbi: BasicBlockIndex) -> bool {
        self.reachable_basic_blocks.contains(&bbi)
    }

    pub fn successors(&self, bbi: BasicBlockIndex) -> &[BasicBlockIndex] {
        self.real_edges.successors(bbi)
    }
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_reachable_basic_blocks(mir: &Mir, real_edges: &RealEdges) -> HashSet<BasicBlock> {
    let mut reachable_basic_blocks: HashSet<BasicBlock> = HashSet::new();
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks().indices().next().unwrap()];

    while !to_visit.is_empty() {
        let source = to_visit.pop().unwrap();

        if visited.contains(&source) {
            continue;
        }

        visited.insert(source);
        reachable_basic_blocks.insert(source);

        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    reachable_basic_blocks
}

fn is_spec_closure(def_id: def_id::DefId, tcx: &TyCtxt) -> bool {
    crate::utils::has_spec_only_attr(crate::utils::get_attributes(*tcx, def_id))
}

pub fn is_marked_specification_block(bb_data: &BasicBlockData, tcx: &TyCtxt) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (_, Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _))) = &stmt.kind {
            if is_spec_closure(*def_id, tcx) {
                return true;
            }
        }
    }
    false
}

pub fn get_loop_invariant<'tcx>(bb_data: &BasicBlockData<'tcx>, tcx: TyCtxt<'tcx>) -> Option<(ProcedureDefId, prusti_rustc_interface::middle::ty::subst::SubstsRef<'tcx>)> {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (_, Rvalue::Aggregate(box AggregateKind::Closure(def_id, substs), _))) = &stmt.kind {
            if is_spec_closure(*def_id, &tcx) && crate::utils::has_prusti_attr(crate::utils::get_attributes(tcx, *def_id), "loop_body_invariant_spec") {
                return Some((*def_id, substs))
            }
        }
    }
    None
}

pub fn is_loop_invariant_block<'tcx>(bb_data: &BasicBlockData<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    get_loop_invariant(bb_data, tcx).is_some()
}

pub fn is_ghost_begin_marker<'tcx>(bb: &BasicBlockData<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    is_spec_block_kind(bb, tcx, "ghost_begin")
}

pub fn is_ghost_end_marker<'tcx>(bb: &BasicBlockData<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    is_spec_block_kind(bb, tcx, "ghost_end")
}

fn is_spec_block_kind(bb_data: &BasicBlockData, tcx: TyCtxt, kind: &str) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (_, Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _))) = &stmt.kind {
            if is_spec_closure(*def_id, &tcx) && crate::utils::has_prusti_attr(crate::utils::get_attributes(tcx, *def_id), kind) {
                return true;
            }
        }
    }
    false
}

#[derive(Debug)]
struct BasicBlockNode {
    successors: HashSet<BasicBlock>,
    predecessors: HashSet<BasicBlock>,
}

fn _blocks_definitely_leading_to<'a>(bb_graph: &'a HashMap<BasicBlock, BasicBlockNode>,
                                 target: BasicBlock,
                                 blocks: &'a mut HashSet<BasicBlock>) -> &'a mut HashSet<BasicBlock> {
    for pred in bb_graph[&target].predecessors.iter() {
        debug!("target: {:#?}, pred: {:#?}", target, pred);
        if bb_graph[pred].successors.len() == 1 {
            debug!("pred {:#?} has 1 successor", pred);
            blocks.insert(*pred);
            _blocks_definitely_leading_to(bb_graph, *pred, blocks);
        }
    }
    blocks
}

fn blocks_definitely_leading_to(bb_graph: &HashMap<BasicBlock, BasicBlockNode>, target: BasicBlock) -> HashSet<BasicBlock> {
    let mut blocks = HashSet::new();
    _blocks_definitely_leading_to(bb_graph, target, &mut blocks);
    blocks
}

fn blocks_dominated_by(mir: &Mir, dominator: BasicBlock) -> HashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut blocks = HashSet::new();
    for bb in mir.basic_blocks().indices() {
        if dominators.is_dominated_by(bb, dominator) {
            blocks.insert(bb);
        }
    }
    blocks
}

fn get_nonspec_basic_blocks(bb_graph: HashMap<BasicBlock, BasicBlockNode>, mir: &Mir, tcx: &TyCtxt) -> HashSet<BasicBlock>{
    let mut spec_basic_blocks: HashSet<BasicBlock> = HashSet::new();
    for (bb, _) in bb_graph.iter() {
        if is_marked_specification_block(&mir[*bb], tcx) {
            spec_basic_blocks.insert(*bb);
            spec_basic_blocks.extend(blocks_definitely_leading_to(&bb_graph, *bb).into_iter());
            spec_basic_blocks.extend(blocks_dominated_by(mir, *bb).into_iter());
        }
    }
    debug!("spec basic blocks: {:#?}", spec_basic_blocks);

    let all_basic_blocks: HashSet<BasicBlock> = bb_graph.keys().cloned().collect();
    all_basic_blocks.difference(&spec_basic_blocks).cloned().collect()
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_nonspec_basic_blocks(mir: &Mir, real_edges: &RealEdges, tcx: &TyCtxt) -> HashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut loop_heads: HashSet<BasicBlock> = HashSet::new();

    for source in mir.basic_blocks().indices() {
        for &target in real_edges.successors(source) {
            if dominators.is_dominated_by(source, target) {
                loop_heads.insert(target);
            }
        }
    }

    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks().indices().next().unwrap()];

    let mut bb_graph: HashMap<BasicBlock, BasicBlockNode> = HashMap::new();

    while !to_visit.is_empty() {
        let source = to_visit.pop().unwrap();

        if visited.contains(&source) {
            continue;
        }

        bb_graph.entry(source).or_insert_with(|| BasicBlockNode {
                successors: HashSet::new(),
                predecessors: HashSet::new(),
            });

        visited.insert(source);

        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {:?} is a loop head", source);
        }
        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }

            bb_graph.entry(target).or_insert_with(|| BasicBlockNode {
                    successors: HashSet::new(),
                    predecessors: HashSet::new(),
                });
            bb_graph.get_mut(&target).unwrap().predecessors.insert(source);
            bb_graph.get_mut(&source).unwrap().successors.insert(target);
        }
    }

    get_nonspec_basic_blocks(bb_graph, mir, tcx)
}
