// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{body::MirBody, loops, EnvName, EnvQuery};
use crate::{
    data::ProcedureDefId,
    environment::{debug_utils::to_text::ToText, mir_utils::RealEdges, Environment},
};
use log::{debug, trace};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    hir::def_id,
    middle::{
        mir::{self, AggregateKind, BasicBlock, BasicBlockData, Body, Rvalue, StatementKind},
        ty::{Ty, TyCtxt},
    },
    span::Span,
};

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'tcx> {
    tcx: TyCtxt<'tcx>,
    env_name: EnvName<'tcx>,
    proc_def_id: ProcedureDefId,
    mir: MirBody<'tcx>,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
    reachable_basic_blocks: FxHashSet<BasicBlock>,
    nonspec_basic_blocks: FxHashSet<BasicBlock>,
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    #[tracing::instrument(name = "Procedure::new", level = "debug", skip(env))]
    pub fn new(env: &Environment<'tcx>, proc_def_id: ProcedureDefId) -> Self {
        let mir = env
            .body
            .get_impure_fn_body_identity(proc_def_id.expect_local());
        let real_edges = RealEdges::new(&mir);
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir, &real_edges);
        let nonspec_basic_blocks = build_nonspec_basic_blocks(env.query, &mir, &real_edges);
        let loop_info = loops::ProcedureLoops::new(&mir, &real_edges);

        Self {
            tcx: env.tcx(),
            env_name: env.name,
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
        let _types: FxHashSet<Ty> = FxHashSet::default();
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

    pub fn get_lifetime_of_var(&self, var: mir::Local) -> Option<String> {
        fn get_lifetime_if_matches(
            local: mir::Local,
            var: mir::Local,
            mir: &Body,
        ) -> Option<String> {
            if local == var {
                let ty_kind = mir.local_decls[local].ty.kind();
                if let prusti_rustc_interface::middle::ty::TyKind::Ref(region, _ty, _mutability) =
                    ty_kind
                {
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

    pub fn get_var_of_lifetime(&self, lft: &str) -> Option<mir::Local> {
        let mir = self.get_mir();
        for local in mir.vars_and_temps_iter() {
            if let prusti_rustc_interface::middle::ty::TyKind::Ref(region, _, _) =
                &mir.local_decls[local].ty.kind()
            {
                if region.to_text() == lft {
                    return Some(local);
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
    pub fn get_mir(&self) -> &Body<'tcx> {
        &self.mir
    }

    /// Get the typing context.
    pub fn get_tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_def_path(&self) -> String {
        self.env_name.get_item_def_path(self.proc_def_id)
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
        self.mir.basic_blocks.indices().next().unwrap()
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
fn build_reachable_basic_blocks(mir: &Body, real_edges: &RealEdges) -> FxHashSet<BasicBlock> {
    let mut reachable_basic_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut visited: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks.indices().next().unwrap()];

    while let Some(source) = to_visit.pop() {
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

fn is_spec_closure(env_query: EnvQuery, def_id: def_id::DefId) -> bool {
    crate::utils::has_spec_only_attr(env_query.get_attributes(def_id))
}

pub fn is_marked_specification_block(env_query: EnvQuery, bb_data: &BasicBlockData) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _),
        )) = &stmt.kind
        {
            if is_spec_closure(env_query, *def_id) {
                return true;
            }
        }
    }
    false
}

pub fn get_loop_invariant<'tcx>(
    env_query: EnvQuery,
    bb_data: &BasicBlockData<'tcx>,
) -> Option<(
    ProcedureDefId,
    prusti_rustc_interface::middle::ty::GenericArgsRef<'tcx>,
)> {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Closure(def_id, substs), _),
        )) = &stmt.kind
        {
            if is_spec_closure(env_query, *def_id)
                && crate::utils::has_prusti_attr(
                    env_query.get_attributes(def_id),
                    "loop_body_invariant_spec",
                )
            {
                return Some((*def_id, substs));
            }
        }
    }
    None
}

pub fn is_loop_invariant_block<'tcx>(env_query: EnvQuery, bb_data: &BasicBlockData<'tcx>) -> bool {
    get_loop_invariant(env_query, bb_data).is_some()
}

pub fn is_loop_variant_block<'tcx>(env_query: EnvQuery, bb: &BasicBlockData<'tcx>) -> bool {
    is_spec_block_kind(env_query, bb, "loop_body_variant_spec")
}

pub fn is_ghost_begin_marker<'tcx>(env_query: EnvQuery, bb: &BasicBlockData<'tcx>) -> bool {
    is_spec_block_kind(env_query, bb, "ghost_begin")
}

pub fn is_ghost_end_marker<'tcx>(env_query: EnvQuery, bb: &BasicBlockData<'tcx>) -> bool {
    is_spec_block_kind(env_query, bb, "ghost_end")
}

fn is_spec_block_kind(env_query: EnvQuery, bb_data: &BasicBlockData, kind: &str) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (
            _,
            Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _),
        )) = &stmt.kind
        {
            if is_spec_closure(env_query, *def_id)
                && crate::utils::has_prusti_attr(env_query.get_attributes(def_id), kind)
            {
                return true;
            }
        }
    }
    false
}

#[derive(Debug)]
struct BasicBlockNode {
    successors: FxHashSet<BasicBlock>,
    predecessors: FxHashSet<BasicBlock>,
}

#[tracing::instrument(level = "debug", skip_all)]
fn _blocks_definitely_leading_to<'a>(
    bb_graph: &'a FxHashMap<BasicBlock, BasicBlockNode>,
    target: BasicBlock,
    blocks: &'a mut FxHashSet<BasicBlock>,
) -> &'a mut FxHashSet<BasicBlock> {
    for pred in bb_graph[&target].predecessors.iter() {
        debug!("target: {target:#?}, pred: {pred:#?}");
        if bb_graph[pred].successors.len() == 1 {
            debug!("pred {pred:#?} has 1 successor");
            blocks.insert(*pred);
            _blocks_definitely_leading_to(bb_graph, *pred, blocks);
        }
    }
    blocks
}

fn blocks_definitely_leading_to(
    bb_graph: &FxHashMap<BasicBlock, BasicBlockNode>,
    target: BasicBlock,
) -> FxHashSet<BasicBlock> {
    let mut blocks = FxHashSet::default();
    _blocks_definitely_leading_to(bb_graph, target, &mut blocks);
    blocks
}

fn blocks_dominated_by(mir: &Body, dominator: BasicBlock) -> FxHashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut blocks = FxHashSet::default();
    for bb in mir.basic_blocks.indices() {
        if dominators.dominates(dominator, bb) {
            blocks.insert(bb);
        }
    }
    blocks
}

#[tracing::instrument(level = "trace", skip_all)]
fn get_nonspec_basic_blocks(
    env_query: EnvQuery,
    bb_graph: FxHashMap<BasicBlock, BasicBlockNode>,
    mir: &Body,
) -> FxHashSet<BasicBlock> {
    let mut spec_basic_blocks: FxHashSet<BasicBlock> = FxHashSet::default();
    for (bb, _) in bb_graph.iter() {
        if is_marked_specification_block(env_query, &mir[*bb]) {
            spec_basic_blocks.insert(*bb);
            spec_basic_blocks.extend(blocks_definitely_leading_to(&bb_graph, *bb));
            spec_basic_blocks.extend(blocks_dominated_by(mir, *bb));
        }
    }
    debug!("spec basic blocks: {spec_basic_blocks:#?}");

    let all_basic_blocks: FxHashSet<BasicBlock> = bb_graph.keys().cloned().collect();
    all_basic_blocks
        .difference(&spec_basic_blocks)
        .cloned()
        .collect()
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_nonspec_basic_blocks(
    env_query: EnvQuery,
    mir: &Body,
    real_edges: &RealEdges,
) -> FxHashSet<BasicBlock> {
    let dominators = mir.basic_blocks.dominators();
    let mut loop_heads: FxHashSet<BasicBlock> = FxHashSet::default();

    for source in mir.basic_blocks.indices() {
        for &target in real_edges.successors(source) {
            if dominators.dominates(target, source) {
                loop_heads.insert(target);
            }
        }
    }

    let mut visited: FxHashSet<BasicBlock> = FxHashSet::default();
    let mut to_visit: Vec<BasicBlock> = vec![mir.basic_blocks.indices().next().unwrap()];

    let mut bb_graph: FxHashMap<BasicBlock, BasicBlockNode> = FxHashMap::default();

    while let Some(source) = to_visit.pop() {
        if visited.contains(&source) {
            continue;
        }

        bb_graph.entry(source).or_insert_with(|| BasicBlockNode {
            successors: FxHashSet::default(),
            predecessors: FxHashSet::default(),
        });

        visited.insert(source);

        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {source:?} is a loop head");
        }
        for &target in real_edges.successors(source) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }

            bb_graph.entry(target).or_insert_with(|| BasicBlockNode {
                successors: FxHashSet::default(),
                predecessors: FxHashSet::default(),
            });
            bb_graph
                .get_mut(&target)
                .unwrap()
                .predecessors
                .insert(source);
            bb_graph.get_mut(&source).unwrap().successors.insert(target);
        }
    }

    get_nonspec_basic_blocks(env_query, bb_graph, mir)
}
