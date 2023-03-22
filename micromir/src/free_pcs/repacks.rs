// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::{fx::FxHashSet, graph::WithStartNode},
    dataflow::{storage, Analysis, ResultsCursor, AnalysisDomain, JoinSemiLattice, CallReturnPlaces,
        impls::{MaybeStorageLive, MaybeBorrowedLocals, MaybeRequiresStorage, MaybeLiveLocals}},
    index::vec::{Idx, IndexVec},
    middle::{
        mir::{Statement, Location, Terminator, Body, BasicBlock, HasLocalDecls, Local, RETURN_PLACE},
        ty::TyCtxt,
    },
};

use crate::{
    CapabilityKind, Place,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepackOp<'tcx> {
    Weaken(Place<'tcx>, CapabilityKind, CapabilityKind),
    // TODO: figure out when and why this happens
    DeallocUnknown(Local),
    DeallocForCleanup(Local),
    // First place is packed up, second is guide place to pack up from
    Pack(Place<'tcx>, Place<'tcx>, CapabilityKind),
    // First place is packed up, second is guide place to unpack to
    Unpack(Place<'tcx>, Place<'tcx>, CapabilityKind),
}
