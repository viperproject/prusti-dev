// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use crate::pcs::{MicroMirStatement, Mutability, TemporaryPlace};
// use rustc_middle::mir::{Operand, Operand::*, Rvalue::*, Statement, StatementKind::*};

// fn translate_individual_statement<'tcx>(
//     current: &mut Vec<MicroMirStatement<'tcx>>,
//     s: &Statement<'tcx>,
// ) -> Result<(), ()> {
//     match &s.kind {
//         Assign(box (pl, Use(Copy(pc)))) => {
//             todo!();
//         }
//         _ => Err(()),
//     }
// }
//
// fn translate_operand<'tcx>(
//     current: &mut Vec<MicroMirStatement<'tcx>>,
//     op: &Operand<'tcx>,
//     into: &TemporaryPlace,
// ) -> Result<(), ()> {
//     match op {
//         // Lookup the mutability from a tcx
//         //
//         Copy(p) => {
//             todo!();
//         }
//         Move(p) => {
//             todo!();
//         }
//         Constant(box k) => {
//             todo!();
//         }
//     }
// }
//
//
//
//
// Ask about current encoding architecutre first...
//      -> How to get place mutability
//      -> Is a place expected to be a borrow?
