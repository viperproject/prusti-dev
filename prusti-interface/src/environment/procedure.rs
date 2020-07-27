// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::loops;
use crate::data::ProcedureDefId;
use rustc_middle::mir::{self, Body as Mir};
use rustc_middle::mir::{BasicBlock, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::cell::Ref;
use std::collections::HashSet;
use rustc_span::Span;
use log::{trace, debug};

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
        let (mir, _) = tcx.mir_validated(ty::WithOptConstParam::unknown(proc_def_id.expect_local()));
        let mir = mir.borrow();
        let reachable_basic_blocks = build_reachable_basic_blocks(&mir);
        let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir);

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
                            ty:
                                &ty::TyS {
                                    kind: ty::TyKind::FnDef(def_id, ..),
                                    ..
                                },
                            ..
                        },
                    ..
                }),
            ..
        } = self.mir[bbi].terminator().kind
        {
            // let func_proc_name = self.tcx.absolute_item_path_str(def_id);
            let func_proc_name = self.tcx.def_path_str(def_id);
            &func_proc_name == "std::panicking::begin_panic"
                || &func_proc_name == "std::rt::begin_panic"
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

        let term = mir[source].terminator();
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

        let term = mir[source].terminator();
        let is_loop_head = loop_heads.contains(&source);
        if is_loop_head {
            trace!("MIR block {:?} is a loop head", source);
        }
        for target in get_normal_targets(term) {
            // FIXME: Filtering is broken.
            if !visited.contains(&target) {
                to_visit.push(target);
            }
        }
    }

    nonspec_basic_blocks
}
