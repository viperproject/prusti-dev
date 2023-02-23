// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::MicroOperand;
use prusti_rustc_interface::{
    middle::{
        mir::{AggregateKind, BinOp, BorrowKind, CastKind, Mutability, NullOp, Place, UnOp},
        ty::{self, Region, Ty},
    },
    span::def_id::DefId,
};

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MicroRvalue<'tcx> {
    Use(MicroOperand),
    Repeat(MicroOperand, ty::Const<'tcx>),
    Ref(Region<'tcx>, BorrowKind, Place<'tcx>),
    ThreadLocalRef(DefId),
    AddressOf(Mutability, Place<'tcx>),
    Len(Place<'tcx>),
    Cast(CastKind, MicroOperand, Ty<'tcx>),
    BinaryOp(BinOp, Box<(MicroOperand, MicroOperand)>),
    CheckedBinaryOp(BinOp, Box<(MicroOperand, MicroOperand)>),
    NullaryOp(NullOp, Ty<'tcx>),
    UnaryOp(UnOp, MicroOperand),
    Discriminant(Place<'tcx>),
    Aggregate(Box<AggregateKind<'tcx>>, Vec<MicroOperand>),
    ShallowInitBox(MicroOperand, Ty<'tcx>),
    CopyForDeref(Place<'tcx>),
}
