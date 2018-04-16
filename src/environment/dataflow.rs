/// Results of MIR dataflow analyses.

use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc::mir;
use rustc_mir::borrow_check::{MirBorrowckCtxt, do_mir_borrowck};
use rustc_mir::borrow_check::flows::Flows;

/// Stores the results of MIR dataflow analyses.
pub struct MirDataflowInfo {
}

pub fn get_info<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, def_id: DefId,
                          mir: &mir::Mir<'tcx>) -> MirDataflowInfo {
    assert!(tcx.nll());
    let opt_closure_req = tcx.infer_ctxt().enter(|infcx| {
        do_mir_borrowck(&infcx, mir, def_id, Some(box callback))
    });
    data.lock().unwrap().take().unwrap()
}


use std::sync::Mutex;

lazy_static! {
static ref data: Mutex<Option<MirDataflowInfo>> = Mutex::new(None);
}

fn callback<'s, 'g, 'gcx, 'tcx>(mbcx: &'s mut MirBorrowckCtxt<'g, 'gcx, 'tcx>, flows: &'s mut Flows<'g, 'gcx, 'tcx>) {
    let mut value = data.lock().unwrap();
    *value = None;
}
