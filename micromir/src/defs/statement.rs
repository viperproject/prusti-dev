// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use core::fmt::{Debug, Formatter, Result};
use prusti_rustc_interface::{
    middle::{
        mir::{
            Coverage, FakeReadCause, Local, NonDivergingIntrinsic, RetagKind, Statement,
            StatementKind, UserTypeProjection,
        },
        ty,
    },
    target::abi::VariantIdx,
};

use crate::{
    MicroCopyNonOverlapping, MicroNonDivergingIntrinsic, MicroRvalue, Operands, Place,
    PlaceCapabilitySummary,
};

#[derive(Clone)]
/// Note that in rare cases an operand and the target of kind can be the same place!
/// For example, the following function:
/// https://github.com/dtolnay/syn/blob/636509368ed9dbfad8bf3d15f84b0046804a1c14/src/bigint.rs#L13-L29
/// generates a `MicroStatement { operands: [Copy(_5), Move(_22)], stmt: _5 = BinaryOp(BitOr, (tmp0, tmp1)) }`
pub struct MicroStatement<'tcx> {
    pub repack_operands: Option<PlaceCapabilitySummary<'tcx>>,
    pub operands: Operands<'tcx>,
    // pub repack_stmt: Option<PlaceCapabilitySummary<'tcx>>,
    pub kind: MicroStatementKind<'tcx>,
}

#[derive(Clone, PartialEq, Hash)]
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
                MicroStatementKind::Assign(box ((*p).into(), operands.translate_rvalue(r)))
            }
            &StatementKind::FakeRead(box (c, p)) => MicroStatementKind::FakeRead(box (c, p.into())),
            &StatementKind::SetDiscriminant {
                box place,
                variant_index,
            } => MicroStatementKind::SetDiscriminant {
                place: box place.into(),
                variant_index: variant_index,
            },
            &StatementKind::Deinit(box p) => MicroStatementKind::Deinit(box p.into()),
            &StatementKind::StorageLive(l) => MicroStatementKind::StorageLive(l),
            &StatementKind::StorageDead(l) => MicroStatementKind::StorageDead(l),
            &StatementKind::Retag(k, box p) => MicroStatementKind::Retag(k, box p.into()),
            StatementKind::AscribeUserType(box (p, ty), v) => {
                MicroStatementKind::AscribeUserType(box ((*p).into(), ty.clone()), *v)
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

impl Debug for MicroStatement<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        let mut dbg = fmt.debug_struct("MicroStatement");
        if let Some(repack) = &self.repack_operands {
            dbg.field("pcs", repack);
        }
        if self.operands.len() > 0 {
            dbg.field("operands", &*self.operands);
        }
        dbg.field("stmt", &self.kind);
        dbg.finish()
    }
}

impl Debug for MicroStatementKind<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        use MicroStatementKind::*;
        match self {
            Assign(box (ref place, ref rv)) => write!(fmt, "{:?} = {:?}", place, rv),
            FakeRead(box (ref cause, ref place)) => {
                write!(fmt, "FakeRead({:?}, {:?})", cause, place)
            }
            Retag(ref kind, ref place) => write!(
                fmt,
                "Retag({}{:?})",
                match kind {
                    RetagKind::FnEntry => "[fn entry] ",
                    RetagKind::TwoPhase => "[2phase] ",
                    RetagKind::Raw => "[raw] ",
                    RetagKind::Default => "",
                },
                place,
            ),
            StorageLive(ref place) => write!(fmt, "StorageLive({:?})", place),
            StorageDead(ref place) => write!(fmt, "StorageDead({:?})", place),
            SetDiscriminant {
                ref place,
                variant_index,
            } => {
                write!(fmt, "discriminant({:?}) = {:?}", place, variant_index)
            }
            Deinit(ref place) => write!(fmt, "Deinit({:?})", place),
            AscribeUserType(box (ref place, ref c_ty), ref variance) => {
                write!(
                    fmt,
                    "AscribeUserType({:?}, {:?}, {:?})",
                    place, variance, c_ty
                )
            }
            Coverage(box self::Coverage {
                ref kind,
                code_region: Some(ref rgn),
            }) => {
                write!(fmt, "Coverage::{:?} for {:?}", kind, rgn)
            }
            Coverage(box ref coverage) => write!(fmt, "Coverage::{:?}", coverage.kind),
            Intrinsic(box ref intrinsic) => write!(fmt, "{intrinsic}"),
            ConstEvalCounter => write!(fmt, "ConstEvalCounter"),
            Nop => write!(fmt, "nop"),
        }
    }
}
