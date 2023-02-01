// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::BTreeSet;

use prusti_rustc_interface::middle::ty::TyCtxt;

use crate::mir_utils::Place;
use prusti_rustc_interface::middle::{mir, ty};

/// Run all tests that involve invoking the compiler
// export PRUSTI_COUPLING_ANALYSIS_TEST=true
// ./x.py run --bin analysis-driver -- --analysis=CouplingAnalysis --sysroot=$(rustc --print sysroot) analysis/tests/test_coupling.rs
pub fn run_coupling_tests<'mir, 'tcx: 'mir>(mir: &'mir mir::Body<'tcx>, ty: TyCtxt<'tcx>) {
    println!("[test]    Running coupling test suite");
    assert_eq!(1 + 1, 2);
    place_impl_helpers(mir, ty.clone());
    println!("[test]    All tests passed");
}

pub(crate) fn place_impl_helpers<'mir, 'tcx: 'mir>(_: &'mir mir::Body<'tcx>, ty: TyCtxt<'tcx>) {
    // p0 == _0
    let p0: Place = (mir::Local::from_usize(0)).into();

    // pd0 == *_0
    let pd0: Place = ty.mk_place_deref(mir::Local::from_usize(0).into()).into();

    // p3d0 = (*_0).3
    let p3d0: Place = ty
        .mk_place_field(
            ty.mk_place_deref(mir::Local::from_usize(0).into()),
            mir::Field::from_usize(3),
            ty.mk_ty(ty::TyKind::Char),
        )
        .into();

    // is_deref()
    assert!(!p0.is_deref());
    assert!(pd0.is_deref());
    assert!(!p3d0.is_deref());

    // siblings()
    //  *_0 => {*_0}
    assert_eq!(pd0.siblings(), Some([pd0.clone()].into()));
    assert_eq!(p0.siblings(), None);
}
