// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::EnvQuery;
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{GenericArgsRef, Ty, TyKind},
    span::Span,
};

pub(super) fn extract_closure_from_ty<'tcx>(
    env_query: EnvQuery<'tcx>,
    ty: Ty<'tcx>,
) -> (
    DefId,                // closure definition
    GenericArgsRef<'tcx>, // closure substitutions
    Span,                 // definition span
    Vec<Ty<'tcx>>,        // input types
    Vec<Ty<'tcx>>,        // upvar types
) {
    match ty.kind() {
        TyKind::Closure(def_id, substs) => {
            let cl_substs = substs.as_closure();
            let sig = cl_substs.sig().skip_binder();
            (
                *def_id,
                substs,
                env_query.get_def_span(def_id),
                sig.inputs()[0].tuple_fields().to_vec(),
                cl_substs.upvar_tys().iter().collect(),
            )
        }
        _ => unreachable!("expected closure type"),
    }
}
