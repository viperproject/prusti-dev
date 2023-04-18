// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Display, Formatter, Result};

use prusti_rustc_interface::middle::mir::Local;

use crate::{CapabilityKind, Place};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepackOp<'tcx> {
    Weaken(Place<'tcx>, CapabilityKind, CapabilityKind),
    // TODO: figure out when and why this happens
    // DeallocUnknown(Local),
    DeallocForCleanup(Local),
    // First place is packed up, second is guide place to pack up from
    Pack(Place<'tcx>, Place<'tcx>, CapabilityKind),
    // First place is packed up, second is guide place to unpack to
    Unpack(Place<'tcx>, Place<'tcx>, CapabilityKind),
}

impl Display for RepackOp<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            RepackOp::Weaken(place, from, to) => write!(f, "Weaken({place:?}, {:?})", (*from - *to).unwrap()),
            RepackOp::DeallocForCleanup(_) => todo!(),
            RepackOp::Pack(to, _, kind) => write!(f, "Pack({to:?}, {kind:?})"),
            RepackOp::Unpack(from, _, kind) => write!(f, "Unpack({from:?}, {kind:?})"),
        }
    }
}
