// This file was taken from the compiler:
// https://github.com/rust-lang/rust/blob/master/compiler/rustc_mir_transform/src/elaborate_drops.rs
// This file is licensed under Apache 2.0
// (https://github.com/rust-lang/rust/blob/86f5e177bca8121e1edc9864023a8ea61acf9034/LICENSE-APACHE)
// and MIT
// (https://github.com/rust-lang/rust/blob/86f5e177bca8121e1edc9864023a8ea61acf9034/LICENSE-MIT).

// Changes:
// + Fix compilation errors.
// + Allow obtaining the elaboration patch (this is the main reason for
//   duplication).

use log::debug;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir::*, ty::TyCtxt};
use rustc_mir_dataflow::{
    impls::MaybeInitializedPlaces, move_paths::LookupResult, on_all_drop_children_bits, Analysis,
    MoveDataParamEnv,
};

/// Returns the set of basic blocks whose unwind edges are known
/// to not be reachable, because they are `drop` terminators
/// that can't drop anything.
pub(super) fn find_dead_unwinds<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    env: &MoveDataParamEnv<'tcx>,
) -> BitSet<BasicBlock> {
    debug!("find_dead_unwinds({:?})", body.span);
    // We only need to do this pass once, because unwind edges can only
    // reach cleanup blocks, which can't have unwind edges themselves.
    let mut dead_unwinds = BitSet::new_empty(body.basic_blocks().len());
    let mut flow_inits = MaybeInitializedPlaces::new(tcx, body, env)
        .into_engine(tcx, body)
        .pass_name("find_dead_unwinds")
        .iterate_to_fixpoint()
        .into_results_cursor(body);
    for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
        let place = match bb_data.terminator().kind {
            TerminatorKind::Drop {
                ref place,
                unwind: Some(_),
                ..
            }
            | TerminatorKind::DropAndReplace {
                ref place,
                unwind: Some(_),
                ..
            } => place,
            _ => continue,
        };

        debug!("find_dead_unwinds @ {:?}: {:?}", bb, bb_data);

        let path = if let LookupResult::Exact(path) = env.move_data.rev_lookup.find(place.as_ref())
        {
            path
        } else {
            debug!("find_dead_unwinds: has parent; skipping");
            continue;
        };

        flow_inits.seek_before_primary_effect(body.terminator_loc(bb));
        debug!(
            "find_dead_unwinds @ {:?}: path({:?})={:?}; init_data={:?}",
            bb,
            place,
            path,
            flow_inits.get()
        );

        let mut maybe_live = false;
        on_all_drop_children_bits(tcx, body, env, path, |child| {
            maybe_live |= flow_inits.contains(child);
        });

        debug!("find_dead_unwinds @ {:?}: maybe_live={}", bb, maybe_live);
        if !maybe_live {
            dead_unwinds.insert(bb);
        }
    }

    dead_unwinds
}
