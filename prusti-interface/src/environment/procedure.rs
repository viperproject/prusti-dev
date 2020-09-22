// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_syntax, box_patterns)]

use super::loops;
use crate::data::ProcedureDefId;
use rustc_middle::mir::{self, Body as Mir, Rvalue, AggregateKind};
use rustc_middle::mir::{BasicBlock, BasicBlockData, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::cell::Ref;
use std::collections::{HashSet, HashMap};
use rustc_span::Span;
use log::{trace, debug};
use rustc_middle::mir::StatementKind;
use rustc_hir::def_id;
use std::iter::FromIterator;

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'a, 'tcx: 'a> {
    tcx: TyCtxt<'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Ref<'a, Mir<'tcx>>,
    loop_info: loops::ProcedureLoops,
    reachable_basic_blocks: HashSet<BasicBlock>,
    nonspec_basic_blocks: HashSet<BasicBlock>,
}

impl<'a, 'tcx> Procedure<'a, 'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub fn new(tcx: TyCtxt<'tcx>, proc_def_id: ProcedureDefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let (mir, _) = tcx.mir_promoted(ty::WithOptConstParam::unknown(proc_def_id.expect_local()));
        let mir = mir.borrow();
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir);
        let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir, &tcx);

        let loop_info = loops::ProcedureLoops::new(&mir);

        Self {
            tcx,
            proc_def_id,
            mir,
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
        let mut types: HashSet<Ty> = HashSet::new();
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

    /// Get an absolute path to this procedure
    pub fn get_def_path(&self) -> String {
        let def_path = self.tcx.def_path(self.proc_def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate());
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

    pub fn is_panic_block(&self, bbi: BasicBlockIndex) -> bool {
        if let TerminatorKind::Call {
            args: ref _args,
            destination: ref _destination,
            func:
                mir::Operand::Constant(box mir::Constant {
                    literal:
                        ty::Const {
                            ty,
                            ..
                        },
                    ..
                }),
            ..
        } = self.mir[bbi].terminator().kind {
            if let ty::TyKind::FnDef(def_id, ..) = ty.kind() {
                // let func_proc_name = self.tcx.absolute_item_path_str(def_id);
                let func_proc_name = self.tcx.def_path_str(*def_id);
                &func_proc_name == "std::panicking::begin_panic"
                    || &func_proc_name == "std::rt::begin_panic"
            } else {
                false
            }
        } else {
            false
        }
    }

    pub fn successors(&self, bbi: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        get_normal_targets(self.mir[bbi].terminator())
    }
}

fn get_normal_targets(terminator: &Terminator) -> Vec<BasicBlock> {
    match terminator.kind {
        TerminatorKind::Goto { ref target } | TerminatorKind::Assert { ref target, .. } => {
            vec![*target]
        }

        TerminatorKind::SwitchInt { ref targets, .. } => targets.clone(),

        TerminatorKind::Resume
        | TerminatorKind::Abort
        | TerminatorKind::Return
        | TerminatorKind::Unreachable => vec![],

        TerminatorKind::DropAndReplace { ref target, .. }
        | TerminatorKind::Drop { ref target, .. } => vec![*target],

        TerminatorKind::Call {
            ref destination, ..
        } => match *destination {
            Some((_, target)) => vec![target],
            None => vec![],
        },

        TerminatorKind::FalseEdge {
            ref real_target, ..
        } => vec![*real_target],

        TerminatorKind::FalseUnwind {
            ref real_target, ..
        } => vec![*real_target],

        TerminatorKind::Yield { .. } | TerminatorKind::GeneratorDrop | TerminatorKind::InlineAsm { .. } => unimplemented!(),
    }
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_reachable_basic_blocks(mir: &Mir) -> HashSet<BasicBlock> {
    let mut reachable_basic_blocks: HashSet<BasicBlock> = HashSet::new();
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut to_visit: Vec<BasicBlock> = vec![];
    to_visit.push(mir.basic_blocks().indices().next().unwrap());

    while !to_visit.is_empty() {
        let source = to_visit.pop().unwrap();

        if visited.contains(&source) {
            continue;
        }

        visited.insert(source);
        reachable_basic_blocks.insert(source);

        let term = mir[source].terminator();
        for target in get_normal_targets(term) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    reachable_basic_blocks
}

fn is_spec_closure(def_id: def_id::DefId, tcx: &TyCtxt) -> bool {
    crate::utils::has_spec_only_attr(tcx.get_attrs(def_id))
}

fn is_spec_basic_block(bb_data: &BasicBlockData, tcx: &TyCtxt) -> bool {
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (_, rvalue)) = &stmt.kind {
            if let Rvalue::Aggregate(box aggr, _) = rvalue {
                if let AggregateKind::Closure(def_id, _) = aggr {
                    if is_spec_closure(*def_id, tcx) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
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
    return blocks;
}

fn blocks_definitely_leading_to<'a>(bb_graph: &HashMap<BasicBlock, BasicBlockNode>, target: BasicBlock) -> HashSet<BasicBlock> {
    let mut blocks = HashSet::new();
    _blocks_definitely_leading_to(bb_graph, target, &mut blocks);
    blocks
}

fn get_nonspec_basic_blocks(bb_graph: HashMap<BasicBlock, BasicBlockNode>, mir: &Mir, tcx: &TyCtxt) -> HashSet<BasicBlock>{
    let mut spec_basic_blocks: HashSet<BasicBlock> = HashSet::new();
    for (bb, _) in bb_graph.iter() {
        if is_spec_basic_block(&mir[*bb], &tcx) {
            spec_basic_blocks.insert(*bb);
            spec_basic_blocks.extend(blocks_definitely_leading_to(&bb_graph, *bb).into_iter());
        }
    }
    debug!("spec basic blocks: {:#?}", spec_basic_blocks);

    let all_basic_blocks: HashSet<BasicBlock> = bb_graph.keys().cloned().collect();
    all_basic_blocks.difference(&spec_basic_blocks).cloned().collect()
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_nonspec_basic_blocks(mir: &Mir, tcx: &TyCtxt) -> HashSet<BasicBlock> {
    let dominators = mir.dominators();
    let mut loop_heads: HashSet<BasicBlock> = HashSet::new();

    for source in mir.basic_blocks().indices() {
        let terminator = &mir[source].terminator;
        if let Some(ref term) = *terminator {
            for target in get_normal_targets(term) {
                if dominators.is_dominated_by(source, target) {
                    loop_heads.insert(target);
                }
            }
        }
    }

    let mut nonspec_basic_blocks: HashSet<BasicBlock> = HashSet::new();
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut to_visit: Vec<BasicBlock> = vec![];
    to_visit.push(mir.basic_blocks().indices().next().unwrap());

    let mut bb_graph: HashMap<BasicBlock, BasicBlockNode> = HashMap::new();

    while !to_visit.is_empty() {
        let source = to_visit.pop().unwrap();

        if visited.contains(&source) {
            continue;
        }

        if !bb_graph.contains_key(&source) {
            bb_graph.insert(source, BasicBlockNode {
                successors: HashSet::new(),
                predecessors: HashSet::new(),
            });
        }

        visited.insert(source);

        let term = mir[source].terminator();
        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {:?} is a loop head", source);
        }
        for target in get_normal_targets(term) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }

            if !bb_graph.contains_key(&target) {
                bb_graph.insert(target, BasicBlockNode {
                    successors: HashSet::new(),
                    predecessors: HashSet::new(),
                });
            }
            bb_graph.get_mut(&target).unwrap().predecessors.insert(source);
            bb_graph.get_mut(&source).unwrap().successors.insert(target);
        }
    }

    get_nonspec_basic_blocks(bb_graph, mir, tcx)
}
