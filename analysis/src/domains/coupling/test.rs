// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::ty::TyCtxt;

// export PRUSTI_COUPLING_ANALYSIS_TEST=true
// ./x.py run --bin analysis-driver -- --analysis=CouplingAnalysis --sysroot=$(rustc --print sysroot) analysis/tests/test_coupling.rs

/// Run all tests involving TyCtxt
pub fn run_coupling_tests<'tcx>(ty: TyCtxt<'tcx>) {
    println!("[test]    Running coupling test suite");
    assert_eq!(1 + 1, 2);
    println!("[test]    All tests passed");
}
