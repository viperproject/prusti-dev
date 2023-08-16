use prusti_rustc_interface::span::def_id::DefId;
use rustc_hash::FxHashMap;
use std::cell::RefCell;

use crate::{
    environment::{polonius_info::PoloniusInfo, Environment},
    specs::typed::DefSpecificationMap,
};

// data that is persistent across queries will be stored here.
thread_local! {
    pub static SPECS: RefCell<Option<DefSpecificationMap>> = RefCell::new(None);
    pub static ENV: RefCell<Option<Environment<'static>>> = RefCell::new(None);
    pub static VERIFIED: RefCell<bool> = RefCell::new(false);
    pub static POLONIUS: RefCell<FxHashMap<DefId, PoloniusInfo<'static, 'static>>> = RefCell::default();
}

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

pub fn verified() -> bool {
    VERIFIED.with(|verified| *verified.borrow())
}

pub fn set_verified() {
    VERIFIED.with(|verified| *verified.borrow_mut() = true);
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
