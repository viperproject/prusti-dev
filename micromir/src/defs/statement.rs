// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    middle::{
        mir::{
            Coverage, FakeReadCause, Local, NonDivergingIntrinsic, Place, RetagKind, Statement,
            StatementKind, UserTypeProjection,
        },
        ty,
    },
    target::abi::VariantIdx,
};

use crate::{
    MicroCopyNonOverlapping, MicroNonDivergingIntrinsic, MicroRvalue, Operands,
    PlaceCapabilitySummary,
};

#[derive(Clone, Debug)]
pub struct MicroStatement<'tcx> {
    pub repack_operands: Option<PlaceCapabilitySummary<'tcx>>,
    pub operands: Operands<'tcx>,
    // pub repack_stmt: Option<PlaceCapabilitySummary<'tcx>>,
    pub kind: MicroStatementKind<'tcx>,
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MicroStatementKind<'tcx> {
    Assign(Box<(Place<'tcx>, MicroRvalue<'tcx>)>),
    FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
    SetDiscriminant {
        place: Box<Place<'tcx>>,
        variant_index: VariantIdx,
    },
    Deinit(Box<Place<'tcx>>),
    StorageLive(Local),
    StorageDead(Local),
    Retag(RetagKind, Box<Place<'tcx>>),
    AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, ty::Variance),
    Coverage(Box<Coverage>),
    Intrinsic(Box<MicroNonDivergingIntrinsic>),
    ConstEvalCounter,
    Nop,
}

impl<'tcx> From<&Statement<'tcx>> for MicroStatement<'tcx> {
    fn from(stmt: &Statement<'tcx>) -> Self {
        let mut operands = Operands::new();
        let kind = match &stmt.kind {
            StatementKind::Assign(box (p, r)) => {
                MicroStatementKind::Assign(box (*p, operands.translate_rvalue(r)))
            }
            StatementKind::FakeRead(box (c, p)) => MicroStatementKind::FakeRead(box (*c, *p)),
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => MicroStatementKind::SetDiscriminant {
                place: box **place,
                variant_index: *variant_index,
            },
            StatementKind::Deinit(box p) => MicroStatementKind::Deinit(box *p),
            StatementKind::StorageLive(l) => MicroStatementKind::StorageLive(*l),
            StatementKind::StorageDead(l) => MicroStatementKind::StorageDead(*l),
            StatementKind::Retag(k, box p) => MicroStatementKind::Retag(*k, box *p),
            StatementKind::AscribeUserType(box (p, ty), v) => {
                MicroStatementKind::AscribeUserType(box (*p, ty.clone()), *v)
            }
            StatementKind::Coverage(box c) => MicroStatementKind::Coverage(box c.clone()),
            StatementKind::Intrinsic(box NonDivergingIntrinsic::Assume(o)) => {
                MicroStatementKind::Intrinsic(box MicroNonDivergingIntrinsic::Assume(
                    operands.translate_operand(o),
                ))
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(c)) => {
                MicroStatementKind::Intrinsic(box MicroNonDivergingIntrinsic::CopyNonOverlapping(
                    MicroCopyNonOverlapping {
                        src: operands.translate_operand(&c.src),
                        dst: operands.translate_operand(&c.dst),
                        count: operands.translate_operand(&c.count),
                    },
                ))
            }
            StatementKind::Nop => MicroStatementKind::Nop,
        };
        MicroStatement {
            repack_operands: None,
            operands,
            // repack_stmt: None,
            kind,
        }
    }
}
