use lazy_static::lazy_static;
use prusti_rustc_interface::{middle::mir, span::def_id::DefId};
use rustc_hash::FxHashMap;
use std::sync::Mutex;

// Store a set of blocks which we check for reachability. Each of them is
// set to false if an error is generated for them, which means they are unreachable
lazy_static! {
    pub static ref REACHABILITY_CHECKS: Mutex<FxHashMap<DefId, FxHashMap<mir::BasicBlock, bool>>> =
        Default::default();
}

// add the location when inserting refute(false) into encoding.
// Assume it's reachable, if we catch an error for it later we know it's not!
pub fn add_reachability_check(def_id: DefId, bb: mir::BasicBlock) {
    let mut map = REACHABILITY_CHECKS.lock().unwrap();
    let entry = map.entry(def_id);
    entry.or_default().insert(bb, true);
}

pub fn set_block_unreachable(def_id: DefId, bb: mir::BasicBlock) {
    println!("Marking block {:?} as unreachable", bb);
    let mut map = REACHABILITY_CHECKS.lock().unwrap();
    let fn_map = map.get_mut(&def_id).unwrap();
    // make sure this location is actually in here
    assert!(fn_map.get(&bb).is_some());
    fn_map.insert(bb, false);
}

pub fn get_reachability_map(def_id: DefId) -> Option<FxHashMap<mir::BasicBlock, bool>> {
    let map = REACHABILITY_CHECKS.lock().unwrap();
    map.get(&def_id).cloned()
}
