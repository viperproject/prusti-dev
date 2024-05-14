//! This module allows storing mir bodies with borrowck facts in a thread-local
//! storage. Unfortunately, thread local storage requires all data stored in it
//! to have a `'static` lifetime. Therefore, we transmute the lifetime `'tcx`
//! away when storing the data. To ensure that nothing gets meessed up, we
//! require the client to provide a witness: an instance of type `TyCtxt<'tcx>`
//! that is used to show that the lifetime that the client provided is indeed
//! `'tcx`.

use prusti_rustc_interface::{
    borrowck::consumers::BodyWithBorrowckFacts,
    data_structures::fx::FxHashMap,
    hir::def_id::LocalDefId,
    middle::{mir, ty::TyCtxt},
};
use std::{cell::RefCell, thread_local};

thread_local! {
    pub static SHARED_STATE_WITH_FACTS:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());
    pub static SHARED_STATE_WITHOUT_FACTS:
        RefCell<FxHashMap<LocalDefId, mir::Body<'static>>> =
        RefCell::new(FxHashMap::default());
}

/// # Safety
///
/// See the module level comment.
pub unsafe fn store_mir_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body_with_facts: BodyWithBorrowckFacts<'tcx>,
) {
    // SAFETY: See the module level comment.
    let body_with_facts: BodyWithBorrowckFacts<'static> =
        unsafe { std::mem::transmute(body_with_facts) };
    SHARED_STATE_WITH_FACTS.with(|state| {
        let mut map = state.borrow_mut();
        assert!(map.insert(def_id, body_with_facts).is_none());
    });
}

/// # Safety
///
/// See the module level comment.
#[allow(clippy::needless_lifetimes)] // We want to be very explicit about lifetimes here.
pub(crate) unsafe fn retrieve_mir_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> BodyWithBorrowckFacts<'tcx> {
    let body_with_facts: BodyWithBorrowckFacts<'static> = SHARED_STATE_WITH_FACTS.with(|state| {
        let mut map = state.borrow_mut();
        map.remove(&def_id).unwrap_or_else(|| {
            panic!("No MIR body found for {:?}", def_id);
        })
    });
    // SAFETY: See the module level comment.
    unsafe { std::mem::transmute(body_with_facts) }
}

/// # Safety
///
/// See the module level comment.
pub unsafe fn store_promoted_mir_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: mir::Body<'tcx>,
) {
    // SAFETY: See the module level comment.
    let body: mir::Body<'static> = unsafe { std::mem::transmute(body) };
    SHARED_STATE_WITHOUT_FACTS.with(|state| {
        let mut map = state.borrow_mut();
        assert!(map.insert(def_id, body).is_none());
    });
}

#[allow(clippy::needless_lifetimes)] // We want to be very explicit about lifetimes here.
pub(crate) unsafe fn retrieve_promoted_mir_body<'tcx>(
    _tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> mir::Body<'tcx> {
    let body_without_facts: mir::Body<'static> = SHARED_STATE_WITHOUT_FACTS.with(|state| {
        let mut map = state.borrow_mut();
        map.remove(&def_id).unwrap()
    });
    // SAFETY: See the module level comment.
    unsafe { std::mem::transmute(body_without_facts) }
}
