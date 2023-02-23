// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::{
        mir::{
            Coverage, FakeReadCause, Local, NonDivergingIntrinsic, Place, RetagKind,
            UserTypeProjection,
        },
        ty::{self},
    },
    target::abi::VariantIdx,
};

use crate::{MicroRvalue, Temporary};

#[derive(Clone, Debug)]
pub struct MicroStatement<'tcx> {
    pub operands: IndexVec<Temporary, ()>,
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
    Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
    ConstEvalCounter,
    Nop,
}
