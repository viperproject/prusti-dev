// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::TyCtxt;
use rustc::mir;
use rustc_data_structures::indexed_vec::Idx;

use prusti_interface::environment::{ProcedureImpl, Procedure};


pub struct BorrowInfo {
    //lifetime,
    //blocking_paths: Vec<_>,
    //blocked_paths: Vec<_>,
}

pub fn compute_borrow_infos<'p, 'a, 'tcx>(
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Vec<BorrowInfo>
    where
        'a: 'p,
        'tcx: 'a
{
    trace!("[compute_borrow_infos] enter name={}", procedure.get_name());
    let mir = procedure.get_mir();
    let return_ty = mir.return_ty();
    trace!("return type: {:?}", return_ty);
    let arg_count = mir.arg_count;
    let mut args_ty = Vec::new();
    for i in 1..arg_count+1 {
        let local = mir::Local::new(i);
        let arg_ty = mir.local_decls[local].ty;
        args_ty.push(arg_ty);
        trace!("arg ({}): {:?}", i, arg_ty);
    }
    trace!("[compute_borrow_infos] exit");
    vec![]
}
