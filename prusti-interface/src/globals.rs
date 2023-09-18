use prusti_rustc_interface::{
    middle::mir,
    span::def_id::{CrateNum, DefId},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;

use crate::{
    environment::{polonius_info::PoloniusInfo, Environment},
    specs::typed::DefSpecificationMap,
};

// data that is persistent across queries will be stored here.
thread_local! {
    pub static CHECK_ERROR: RefCell<bool> = RefCell::new(false);
    pub static SPECS: RefCell<Option<DefSpecificationMap>> = RefCell::new(None);
    pub static ENV: RefCell<Option<Environment<'static>>> = RefCell::new(None);
    pub static VERIFIED: RefCell<FxHashSet<CrateNum>> = RefCell::new(Default::default());
    pub static POLONIUS: RefCell<FxHashMap<DefId, PoloniusInfo<'static, 'static>>> = RefCell::default();
    pub static REACHABILITY_CHECKS: RefCell<FxHashMap<DefId, FxHashMap<mir::BasicBlock, bool>>> =
        Default::default();
    // for each encoded assertion, after verification stores true if this assertion
    // will never panic, or false if it possibly panics (after verification)
    pub static VERIFIED_ASSERTIONS: RefCell<FxHashMap<DefId, FxHashMap<mir::BasicBlock, bool>>> = Default::default();
}

pub fn set_check_error() {
    CHECK_ERROR.with(|cell| *cell.borrow_mut() = true)
}

pub fn get_check_error() -> bool {
    CHECK_ERROR.with(|cell| *cell.borrow())
}

/// If we encoded assertions in the hope of being able to eliminate them, we
/// store their locations here, so we can later eliminate them in case they
/// don't generate an error
pub fn add_encoded_assertion(def_id: DefId, bb: mir::BasicBlock) {
    VERIFIED_ASSERTIONS.with(|cell| {
        let mut map = cell.borrow_mut();
        let entry = map.entry(def_id);
        // insert true first, if it generates an error set if to false
        // (if it doesnt generate an error it's either unreachable, or
        // actually verifiably true and can be removed later)
        entry.or_default().insert(bb, true);
    })
}

/// Mark an assertion as violated, meaning we can not eliminate it.
pub fn set_assertion_violated(def_id: DefId, bb: mir::BasicBlock) {
    VERIFIED_ASSERTIONS.with(|cell| {
        let mut map = cell.borrow_mut();
        let fn_map = map.get_mut(&def_id).unwrap();
        assert!(fn_map.get(&bb).is_some());
        fn_map.insert(bb, false);
    })
}

/// For each function returns a map telling us which assertions can be eliminated
pub fn get_assertion_map(def_id: DefId) -> Option<FxHashMap<mir::BasicBlock, bool>> {
    VERIFIED_ASSERTIONS.with(|cell| {
        let map = cell.borrow();
        map.get(&def_id).cloned()
    })
}

// Add the location when inserting refute(false) into encoding.
// Assume it's reachable, if we catch an error for it later we know it's not!
pub fn add_reachability_check(def_id: DefId, bb: mir::BasicBlock) {
    REACHABILITY_CHECKS.with(|cell| {
        let mut map = cell.borrow_mut();
        let entry = map.entry(def_id);
        entry.or_default().insert(bb, true);
    })
}

pub fn set_block_unreachable(def_id: DefId, bb: mir::BasicBlock) {
    REACHABILITY_CHECKS.with(|cell| {
        let mut map = cell.borrow_mut();
        let fn_map = map.get_mut(&def_id).unwrap();
        // make sure this location is actually in here
        assert!(fn_map.get(&bb).is_some());
        fn_map.insert(bb, false);
    })
}

pub fn get_reachability_map(def_id: DefId) -> Option<FxHashMap<mir::BasicBlock, bool>> {
    REACHABILITY_CHECKS.with(|cell| {
        let map = cell.borrow();
        map.get(&def_id).cloned()
    })
}

/// Store specifications and environment.
pub fn store_spec_env<'tcx>(def_spec: DefSpecificationMap, env: Environment<'tcx>) {
    let static_env: Environment<'static> = unsafe { std::mem::transmute(env) };
    SPECS.with(|specs| {
        *specs.borrow_mut() = Some(def_spec);
    });
    ENV.with(|env| {
        *env.borrow_mut() = Some(static_env);
    })
}

pub fn get_defspec() -> DefSpecificationMap {
    SPECS.with(|specs| specs.take().unwrap())
}

pub fn get_env<'tcx>() -> Environment<'tcx> {
    let env_static = ENV.with(|env| env.take().unwrap());
    let env: Environment<'tcx> = unsafe { std::mem::transmute(env_static) };
    env
}

/// Whether verification has already been executed for a specific crate
pub fn verified(krate_id: CrateNum) -> bool {
    VERIFIED.with(|verified| verified.borrow().contains(&krate_id))
}

/// Mark a crate as verified
pub fn set_verified(krate_id: CrateNum) {
    VERIFIED.with(|verified| verified.borrow_mut().insert(krate_id));
}

pub fn store_polonius_info(def_id: DefId, polonius_info: PoloniusInfo<'_, '_>) {
    // very unsafe, why do I have to do this..
    // have to make sure addresses in env stay accurate
    let static_info: PoloniusInfo<'static, 'static> = unsafe { std::mem::transmute(polonius_info) };
    POLONIUS.with(|info| info.borrow_mut().insert(def_id, static_info));
}

// first lifetime corresponds to lifetime of env
pub fn get_polonius_info<'a, 'tcx>(def_id: DefId) -> Option<PoloniusInfo<'a, 'tcx>> {
    let static_polonius = POLONIUS.with(|info| info.borrow_mut().remove(&def_id));
    unsafe { std::mem::transmute(static_polonius) }
}
