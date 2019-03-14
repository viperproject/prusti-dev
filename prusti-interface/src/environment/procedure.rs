// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::mir;
use rustc::ty::{self, Ty, TyCtxt};
use rustc_data_structures::indexed_vec::{IndexVec, Idx};
use std::collections::HashSet;
use std::collections::HashMap;
use rustc::mir::Mir;
use std::cell::Ref;
use rustc::mir::{BasicBlock, BasicBlockData, Terminator, TerminatorKind};
use data::ProcedureDefId;
use syntax::codemap::Span;
use super::loops;

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub struct Procedure<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Ref<'a, Mir<'tcx>>,
    reachable_basic_blocks: HashSet<BasicBlock>,
    nonspec_basic_blocks: HashSet<BasicBlock>,
    predecessors: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>>,
    ordered_basic_blocks: Vec<BasicBlockIndex>,
}

impl<'a, 'tcx> Procedure<'a, 'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, proc_def_id: ProcedureDefId) -> Self {
        let mir = tcx.mir_validated(proc_def_id).borrow();
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir);
        let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir);

        let mut predecessors = HashMap::new();
        for bbi in mir.basic_blocks().indices() {
            let bb_data = &mir.basic_blocks()[bbi];
            let term = bb_data.terminator.as_ref().unwrap();
            for succ in get_normal_targets(term) {
                predecessors.entry(succ)
                    .or_insert(HashSet::new())
                    .insert(bbi);
            }
        }

        let ordered_basic_blocks = Self::order_basic_blocks(&mir);

        Self {
            tcx,
            proc_def_id,
            mir,
            reachable_basic_blocks,
            nonspec_basic_blocks,
            predecessors,
            ordered_basic_blocks,
        }
    }

    /// Returns the list of basic blocks ordered in the topological order.
    fn order_basic_blocks(mir: &Mir<'tcx>) -> Vec<BasicBlockIndex> {
        let basic_blocks = mir.basic_blocks();
        let mut sorted_blocks = Vec::new();
        let mut permanent_mark = IndexVec::<BasicBlockIndex, bool>::from_elem_n(
            false, basic_blocks.len());
        let mut temporary_mark = permanent_mark.clone();
        let loop_info = loops::ProcedureLoops::new(&mir);
        let back_edges = loop_info.back_edges.into_iter().collect();

        fn visit<'tcx>(basic_blocks: &IndexVec<BasicBlock, BasicBlockData<'tcx>>,
                       back_edges: &HashSet<(mir::BasicBlock, mir::BasicBlock)>,
                       current: BasicBlockIndex,
                       sorted_blocks: &mut Vec<BasicBlockIndex>,
                       permanent_mark: &mut IndexVec<BasicBlockIndex, bool>,
                       temporary_mark: &mut IndexVec<BasicBlockIndex, bool>) {
            if permanent_mark[current] {
                return;
            }
            assert!(!temporary_mark[current], "Not a DAG!");
            temporary_mark[current] = true;
            for &successor in basic_blocks[current].terminator().successors() {
                if back_edges.contains(&(current, successor)) {
                    continue;
                }
                visit(basic_blocks, back_edges, successor,
                      sorted_blocks, permanent_mark, temporary_mark);
            }
            permanent_mark[current] = true;
            sorted_blocks.push(current);
        }

        loop {
            let index = if let Some(index) = permanent_mark.iter().position(|x| !*x) {
                BasicBlockIndex::new(index)
            } else {
                break
            };
            visit(basic_blocks, &back_edges, index,
                  &mut sorted_blocks, &mut permanent_mark, &mut temporary_mark);
        }
        sorted_blocks.reverse();
        sorted_blocks
    }

    pub fn predecessors(&self, bbi: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        self.predecessors.get(&bbi)
            .map(|p| p.iter().cloned().collect())
            .unwrap_or(vec![])
    }

    /// Returns all the types used in the procedure, and any types reachable from them
    pub fn get_declared_types(&self) -> Vec<Ty<'tcx>> {
        let mut types: HashSet<Ty> = HashSet::new();
        for var in &self.mir.local_decls {
            for ty in var.ty.walk() {
                let declared_ty = ty;
                //let declared_ty = clean_type(tcx, ty);
                //let declared_ty = tcx.erase_regions(&ty);
                types.insert(declared_ty);
            }
        }
        types.into_iter().collect()
    }

    /// Get definition ID of the procedure.
    pub fn get_id(&self) -> ProcedureDefId { self.proc_def_id }

    /// Get the MIR of the procedure
    pub fn get_mir(&self) -> &Mir<'tcx> {
        &self.mir
    }

    /// Get an absolute path to this procedure
    pub fn get_def_path(&self) -> String {
        let def_path = self.tcx.def_path(self.proc_def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate());
        crate_name
    }

    /// Get a short name of the procedure
    pub fn get_short_name(&self) -> String {
        self.tcx.item_path_str(self.proc_def_id)
    }

    /// Get a readable path of the procedure
    pub fn get_name(&self) -> String {
        self.tcx.absolute_item_path_str(self.proc_def_id)
    }

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
        self.ordered_basic_blocks.clone()
    }

    /// Iterate over all reachable CFG basic blocks
    pub fn get_reachable_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.get_all_cfg_blocks().into_iter()
            .filter(|bbi| self.is_reachable_block(*bbi))
            .collect()
    }

    /// Iterate over all reachable CFG basic blocks that are not part of the specification type checking
    pub fn get_reachable_nonspec_cfg_blocks(&self) -> Vec<BasicBlock> {
        self.get_reachable_cfg_blocks().into_iter()
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
            func: mir::Operand::Constant(
                box mir::Constant {
                    literal: mir::Literal::Value {
                        value: ty::Const {
                            ty: &ty::TyS {
                                sty: ty::TyFnDef(def_id, ..),
                                ..
                            },
                            ..
                        }
                    },
                    ..
                }
            ),
            ..
        } = self.mir[bbi].terminator.as_ref().unwrap().kind {
            let func_proc_name = self.tcx.absolute_item_path_str(def_id);
            &func_proc_name == "std::panicking::begin_panic" ||
                &func_proc_name == "std::rt::begin_panic"
        } else {
            false
        }
    }

    pub fn successors(&self, bbi: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        get_normal_targets(self.mir[bbi].terminator.as_ref().unwrap())
    }
}

fn get_normal_targets(terminator: &Terminator) -> Vec<BasicBlock> {
    match terminator.kind {
        TerminatorKind::Goto { ref target } |
        TerminatorKind::Assert { ref target, .. } =>
            vec![*target],

        TerminatorKind::SwitchInt { ref targets, .. } =>
            targets.clone(),

        TerminatorKind::Resume |
        TerminatorKind::Abort |
        TerminatorKind::Return |
        TerminatorKind::Unreachable =>
            vec![],

        TerminatorKind::DropAndReplace { ref target, .. } |
        TerminatorKind::Drop { ref target, .. } =>
            vec![*target],

        TerminatorKind::Call { ref destination, .. } => {
            match *destination {
                Some((_, target)) => vec![target],
                None => vec![]
            }
        }

        TerminatorKind::FalseEdges { ref real_target, .. } => vec![*real_target],

        TerminatorKind::FalseUnwind { ref real_target, .. } => vec![*real_target],

        TerminatorKind::Yield { .. } |
        TerminatorKind::GeneratorDrop => unimplemented!(),
    }
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_reachable_basic_blocks<'tcx>(mir: &Mir<'tcx>) -> HashSet<BasicBlock> {
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

        let term = mir[source].terminator.as_ref().unwrap();
        for target in get_normal_targets(term) {
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    reachable_basic_blocks
}

/// Returns the set of basic blocks that are not used as part of the typechecking of Prusti specifications
fn build_nonspec_basic_blocks<'tcx>(mir: &Mir<'tcx>) -> HashSet<BasicBlock> {
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

    while !to_visit.is_empty() {
        let source = to_visit.pop().unwrap();

        if visited.contains(&source) {
            continue;
        }

        visited.insert(source);
        nonspec_basic_blocks.insert(source);

        let term = mir[source].terminator.as_ref().unwrap();
        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {:?} is a loop head", source);
        }
        for target in get_normal_targets(term) {
            trace!("Try target {:?} of {:?}", target, source);
            // Skip the following "if false"
            // TODO: this is an approximation: it treats all `if false {...}` as specification blocks
            let target_term = &mir[target].terminator.as_ref().unwrap();
            trace!("target_term {:?}", target_term);
            if let TerminatorKind::SwitchInt { ref discr, ref values, ref targets, .. } = target_term.kind {
                trace!("target_term is a SwitchInt");
                trace!("discr: '{:?}'", discr);
                if format!("{:?}", discr) == "const false" {
                    // Some assumptions
                    assert_eq!(values[0], 0 as u128);
                    assert_eq!(values.len(), 1);

                    // Do not visit the 'then' branch.
                    // So, it will not be put into nonspec_basic_blocks.
                    debug!("MIR block {:?} is the head of a specification branch", targets[1]);
                    visited.insert(targets[1]);
                }
            }
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    nonspec_basic_blocks
}
