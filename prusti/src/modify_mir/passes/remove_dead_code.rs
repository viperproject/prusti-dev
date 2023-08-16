use prusti_interface::environment::inserted_locations_store;
use prusti_rustc_interface::{
    middle::{
        mir::{self, visit::MutVisitor},
        ty::TyCtxt,
    },
    span::def_id::DefId,
};
use rustc_hash::FxHashSet;

pub struct DeadCodeElimination<'tcx> {
    tcx: TyCtxt<'tcx>,
    unreachable_blocks: FxHashSet<mir::BasicBlock>,
}

impl<'tcx, 'a> DeadCodeElimination<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        // collect all the blocks that were inserted but didnt generate
        // a verification error:
        let reachability_map =
            inserted_locations_store::get_reachability_map(def_id).unwrap_or_default();
        let unreachable_blocks: FxHashSet<mir::BasicBlock> = reachability_map
            .iter()
            .filter_map(|(bb, reachable)| (!reachable).then_some(*bb))
            .collect();
        println!(
            "unreachable blocks for method: {:?}, {:#?}",
            def_id, unreachable_blocks
        );
        Self {
            tcx,
            unreachable_blocks,
        }
    }

    pub fn run(&mut self, body: &mut mir::Body<'tcx>) {
        if self.unreachable_blocks.is_empty() {
            return;
        }
        self.visit_body(body);
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for DeadCodeElimination<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut mir::Terminator<'tcx>,
        location: mir::Location,
    ) {
        let new_term_opt = match &mut terminator.kind {
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                // filter out unreachable blocks
                let mut targets_vec: Vec<(u128, mir::BasicBlock)> = targets
                    .iter()
                    .filter_map(|(value, bb)| {
                        (!self.unreachable_blocks.contains(&bb)).then_some((value, bb))
                    })
                    .collect();
                let otherwise_opt = if !self.unreachable_blocks.contains(&targets.otherwise()) {
                    Some(targets.otherwise())
                } else {
                    // unreachable otherwise block, take one of the
                    // targets
                    targets_vec.pop().map(|tup| tup.1)
                };
                if let Some(otherwise) = otherwise_opt {
                    if targets_vec.len() == 0 {
                        Some(mir::TerminatorKind::Goto { target: otherwise })
                    } else {
                        let switch_targets =
                            mir::terminator::SwitchTargets::new(targets_vec.into_iter(), otherwise);
                        if switch_targets.all_targets().len() != targets.all_targets().len() {
                            println!("SwitchInt in block {:?} was changed", location.block);
                        }
                        Some(mir::TerminatorKind::SwitchInt {
                            discr: discr.clone(),
                            targets: switch_targets,
                        })
                    }
                } else {
                    // if none of the targets is reachable, then this block
                    // must be unreachable itself!!
                    // make it actually unreachable?
                    Some(mir::TerminatorKind::Unreachable)
                }
            }
            // potentially perform some checks on sanity of our results.
            // E.g. a goto to a unreachable block can only come from
            // another unreachable block.
            _ => None,
        };
        if let Some(new_term) = new_term_opt {
            terminator.kind = new_term;
        }
    }
}
