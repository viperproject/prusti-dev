use crate::modify_mir::mir_helper::is_check_block;
use prusti_interface::{
    environment::{blocks_dominated_by, is_check_closure, EnvQuery, Environment},
    globals,
    specs::typed::DefSpecificationMap,
};
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{self, patch::MirPatch, visit::MutVisitor},
        ty::{self, TyCtxt},
    },
    span::{def_id::DefId, DUMMY_SP},
};

pub struct RemoveCheckBlocks<'tcx> {
    env_query: EnvQuery<'tcx>,
}

struct SwitchIntBlock {
    block: mir::BasicBlock,
    check_target: mir::BasicBlock,
}

impl<'tcx> RemoveCheckBlocks<'tcx> {
    fn run(tcx: TyCtxt<'tcx>, body: &mut mir::Body<'tcx>) -> Result<(), ()> {
        let mut adjust_blocks = vec![];
        let env_query = EnvQuery::new(tcx);
        // identify switchInts in front of check_blocks
        for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
            if let Some(
                term @ mir::Terminator {
                    kind: mir::TerminatorKind::SwitchInt { .. },
                    ..
                },
            ) = bb_data.terminator
            {
                for target_bb in term.successors() {
                    let bb_data = body.basic_blocks.basic_blocks.get(target_bb).unwrap();
                    if is_check_block(env_query, bb_data) {
                        adjust_blocks.push(SwitchIntBlock {
                            block: bb,
                            check_target: target_bb,
                        })
                    }
                }
            }
        }
        // simplify the switchInt blocks:
        for remove_target in adjust_blocks.into_iter() {

        }

        Ok(())
    }
}
