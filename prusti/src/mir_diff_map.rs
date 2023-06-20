use prusti_rustc_interface::{
    middle::{
        mir::{self, patch::MirPatch, Body, TerminatorKind},
        ty::{self, TyCtxt},
    },
    span::{self, def_id::DefId},
};
use rustc_hash::FxHashMap;

// for each location of calls in a mir_promoted body, map it to its new
// location in the mir_drops_elaborated body
// certain statements are added / removed during this phase,
fn location_map<'tcx>(mut mir_promoted: Body<'tcx>, mut mir_elaborated: Body<'tcx>) -> Result<FxHashMap<mir::Location, mir::Location>,()> {
    // we assume statements are not moved accross blocks (which seems to be accurate)
    let bblocks1 = mir_promoted.basic_blocks.as_mut();
    let bblocks2 = mir_elaborated.basic_blocks.as_mut();
    assert!(bblocks1.len() == bblocks2.len());
    for (block, blockdata1) in bblocks1.clone().into_iter_enumerated() {
        let blockdata2 = bblocks2.get(block);

    }
    Err(())
}



