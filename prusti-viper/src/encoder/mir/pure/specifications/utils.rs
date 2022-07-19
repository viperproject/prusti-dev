// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::{ty, ty::subst::SubstsRef},
    span::Span,
};

pub(super) fn extract_closure_from_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> (
    DefId,             // closure definition
    SubstsRef<'tcx>,   // closure substitutions
    Span,              // definition span
    Vec<ty::Ty<'tcx>>, // input types
    Vec<ty::Ty<'tcx>>, // upvar types
) {
    match ty.kind() {
        ty::TyKind::Closure(def_id, substs) => {
            let cl_substs = substs.as_closure();
            let sig = cl_substs.sig().skip_binder();
            (
                *def_id,
                substs,
                tcx.def_span(*def_id),
                sig.inputs()[0].tuple_fields().to_vec(),
                cl_substs.upvar_tys().collect(),
            )
        }
        _ => unreachable!("expected closure type"),
    }
}
