// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{MicroOperand, Operands};
use prusti_rustc_interface::{
    middle::{
        mir::{
            AggregateKind, BinOp, BorrowKind, CastKind, Mutability, NullOp, Place, Rvalue, UnOp,
        },
        ty::{self, Region, Ty},
    },
    span::def_id::DefId,
};

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MicroNonDivergingIntrinsic {
    Assume(MicroOperand),
    CopyNonOverlapping(MicroCopyNonOverlapping),
}
#[derive(Clone, Debug, PartialEq, Hash)]
pub struct MicroCopyNonOverlapping {
    pub src: MicroOperand,
    pub dst: MicroOperand,
    pub count: MicroOperand,
}

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

impl<'tcx> Operands<'tcx> {
    pub(crate) fn translate_rvalue(&mut self, rvalue: &Rvalue<'tcx>) -> MicroRvalue<'tcx> {
        match rvalue {
            Rvalue::Use(o) => MicroRvalue::Use(self.translate_operand(o)),
            Rvalue::Repeat(o, c) => MicroRvalue::Repeat(self.translate_operand(o), *c),
            Rvalue::Ref(r, bk, p) => MicroRvalue::Ref(*r, *bk, *p),
            Rvalue::ThreadLocalRef(d) => MicroRvalue::ThreadLocalRef(*d),
            Rvalue::AddressOf(m, p) => MicroRvalue::AddressOf(*m, *p),
            Rvalue::Len(p) => MicroRvalue::Len(*p),
            Rvalue::Cast(ck, o, ty) => MicroRvalue::Cast(*ck, self.translate_operand(o), *ty),
            Rvalue::BinaryOp(op, box (opa, opb)) => MicroRvalue::BinaryOp(
                *op,
                box (self.translate_operand(opa), self.translate_operand(opb)),
            ),
            Rvalue::CheckedBinaryOp(op, box (opa, opb)) => MicroRvalue::CheckedBinaryOp(
                *op,
                box (self.translate_operand(opa), self.translate_operand(opb)),
            ),
            Rvalue::NullaryOp(op, ty) => MicroRvalue::NullaryOp(*op, *ty),
            Rvalue::UnaryOp(op, o) => MicroRvalue::UnaryOp(*op, self.translate_operand(o)),
            Rvalue::Discriminant(p) => MicroRvalue::Discriminant(*p),
            Rvalue::Aggregate(ak, ops) => MicroRvalue::Aggregate(
                ak.clone(),
                ops.iter().map(|o| self.translate_operand(o)).collect(),
            ),
            Rvalue::ShallowInitBox(o, ty) => {
                MicroRvalue::ShallowInitBox(self.translate_operand(o), *ty)
            }
            Rvalue::CopyForDeref(p) => MicroRvalue::CopyForDeref(*p),
        }
    }
}
