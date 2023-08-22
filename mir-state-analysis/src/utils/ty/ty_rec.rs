// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    dataflow::storage,
    index::bit_set::BitSet,
    middle::{
        mir::{
            tcx::PlaceTy, Body, HasLocalDecls, Local, Mutability, Place as MirPlace,
            ProjectionElem,
        },
        ty::{Ty, TyKind, TyCtxt},
    },
};

use crate::utils::ty::{DeepTypeVisitor, DeepTypeVisitable, Stack};

pub fn is_ty_rec<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    struct RecTyWalk<'tcx>(TyCtxt<'tcx>, bool);
    impl<'tcx> DeepTypeVisitor<'tcx> for RecTyWalk<'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.0
        }

        fn visit_rec(&mut self, ty: Ty<'tcx>, stack: &mut Stack<'tcx>) {
            if stack.get().contains(&ty) {
                self.1 = true;
                return;
            }
            ty.visit_with(self, stack);
        }
    }
    let mut walker = RecTyWalk(tcx, false);
    walker.visit(ty);
    walker.1
}
