use lazy_static::lazy_static;
use prusti_rustc_interface::{middle::mir, span::def_id::DefId};
use rustc_hash::FxHashMap;
use std::sync::Mutex;

// locations contained in this map are inserted to check for reachability
// If the contained boolean is set to true, this means it generated an error.
// Generating an error in this context means this location is reachable
//
// At some point it might be smarter to pack this into an argument to verify,
// so we don't access the static global from encoding, but at least for
// passing it between queries and after_analysis (and back) it has to be
// a static global
lazy_static! {
    pub static ref INSERTED_LOCATIONS: Mutex<FxHashMap<DefId, FxHashMap<mir::Location, bool>>> =
        Default::default();
}

pub fn add_location(def_id: DefId, loc: mir::Location) {
    let mut map = INSERTED_LOCATIONS.lock().unwrap();
    let entry = map.entry(def_id);
    entry.or_default().insert(loc, false);
}

pub fn contains(def_id: DefId, loc: mir::Location) -> bool {
    let map = INSERTED_LOCATIONS.lock().unwrap();
    if let Some(function_map) = map.get(&def_id) {
        function_map.contains_key(&loc)
    } else {
        false
    }
}

pub fn set_reachable(def_id: DefId, loc: mir::Location) {
    let mut map = INSERTED_LOCATIONS.lock().unwrap();
    let fn_map = map.get_mut(&def_id).unwrap();
    // make sure this location is actually in here
    assert!(fn_map.get(&loc).is_some());
    fn_map.insert(loc, true);
}

pub fn get_function_map(def_id: DefId) -> Option<FxHashMap<mir::Location, bool>> {
    let map = INSERTED_LOCATIONS.lock().unwrap();
    map.get(&def_id).cloned()
}
