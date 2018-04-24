use rustc::mir;
use rustc::ty::{Ty, TyCtxt};
use std::collections::HashSet;
use rustc::mir::Mir;
use std::cell::Ref;
use rustc::mir::Terminator;
use rustc::mir::BasicBlock;
use rustc::mir::TerminatorKind;
use data::ProcedureDefId;

/// Index of a Basic Block
pub type BasicBlockIndex = mir::BasicBlock;

/// A Basic Block Data
pub type BasicBlockData<'tcx> = mir::BasicBlockData<'tcx>;

/// A facade that provides information about the Rust procedure.
pub trait Procedure<'tcx> {
    /// Get definition ID of the procedure.
    fn get_id(&self) -> ProcedureDefId;

    /// Get the MIR of the procedure
    fn get_mir(&self) -> &mir::Mir<'tcx>;

    /// Get the name of the procedure
    fn get_name(&self) -> String;

    /// Iterate over all CFG basic blocks
    fn walk_once_raw_cfg<F>(&self, visitor: F) where F: FnMut(BasicBlockIndex, &BasicBlockData<'tcx>);

    /// Iterate over all CFG basic blocks that are not part of the specification type checking
    fn walk_once_cfg<F>(&self, visitor: F) where F: FnMut(BasicBlockIndex, &BasicBlockData<'tcx>);
}

/// An implementation of the Procedure interface
pub struct ProcedureImpl<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Ref<'a, Mir<'tcx>>,
    nonspec_basic_blocks: HashSet<BasicBlock>,
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
        } else {
            visited.insert(source);
            nonspec_basic_blocks.insert(source);
        }

        let terminator = &mir[source].terminator;
        if let Some(ref term) = *terminator {
            let is_loop_head = loop_heads.contains(&source);
            if is_loop_head {
                debug!("MIR block {:?} is a loop head", source);
            }
            for target in get_normal_targets(term) {
                if is_loop_head {
                    // Skip the following "if false"
                    let target_terminator = &mir[target].terminator;
                    if let Some(ref target_term) = *target_terminator {
                        if let TerminatorKind::SwitchInt { ref discr, ref values, ref targets, .. } = target_term.kind {
                            if format!("{:?}", discr) == "const false" {
                                // Some assumptions
                                assert!(values[0] == 0 as u128);
                                assert!(values.len() == 1);

                                // Do not visit the 'then' branch.
                                // So, it will not be put into nonspec_basic_blocks.
                                debug!("MIR block {:?} is the head of a specification branch", targets[1]);
                                visited.insert(targets[1]);
                            }
                        }
                    }
                }
                if !visited.contains(&target) {
                    to_visit.push(target);
                }
            }
        }
    }

    nonspec_basic_blocks
}

impl<'a, 'tcx> ProcedureImpl<'a, 'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, proc_def_id: ProcedureDefId) -> Self {
        let mir = tcx.mir_validated(proc_def_id).borrow();
        let nonspec_basic_blocks = build_nonspec_basic_blocks(&mir);
        ProcedureImpl { tcx, proc_def_id, mir, nonspec_basic_blocks }
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
}

impl<'a, 'tcx> Procedure<'tcx> for ProcedureImpl<'a, 'tcx> {
    fn get_id(&self) -> ProcedureDefId { self.proc_def_id }

    fn get_mir(&self) -> &Mir<'tcx> {
        &self.mir
    }

    fn get_name(&self) -> String {
        self.tcx.item_path_str(self.proc_def_id)
    }

    fn walk_once_raw_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlock, &BasicBlockData<'tcx>) {
        let basic_blocks = self.mir.basic_blocks();
        for bbi in basic_blocks.indices() {
            let bb_data = &basic_blocks[bbi];
            visitor(bbi, bb_data);
        }
    }

    fn walk_once_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlock, &BasicBlockData<'tcx>) {
        let basic_blocks = self.mir.basic_blocks();
        for bbi in basic_blocks.indices() {
            if self.nonspec_basic_blocks.contains(&bbi) {
                let bb_data = &basic_blocks[bbi];
                visitor(bbi, bb_data);
            }
        }
    }
}
