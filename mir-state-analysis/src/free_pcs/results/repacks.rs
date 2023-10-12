// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::{Display, Formatter, Result};

use prusti_rustc_interface::middle::mir::Local;

use crate::{free_pcs::CapabilityKind, utils::Place};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RepackOp<'tcx> {
    /// Rust will sometimes join two BasicBlocks where a local is live in one and dead in the other.
    /// Our analysis will join these two into a state where the local is dead, and this Op marks the
    /// edge from where it was live.
    ///
    /// This is not an issue in the MIR since it generally has a
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// right after the merge point, which is fine in Rust semantics, since
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// is a no-op if the local is already (conditionally) dead.
    ///
    /// This Op only appears for edges between basic blocks. It is often emitted for edges to panic
    /// handling blocks, but can also appear in regular code for example in the MIR of
    /// [this function](https://github.com/dtolnay/syn/blob/3da56a712abf7933b91954dbfb5708b452f88504/src/attr.rs#L623-L628).
    StorageDead(Local),
    /// This Op only appears within a BasicBlock and is attached to a
    /// [`mir::StatementKind::StorageDead`](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.StatementKind.html#variant.StorageDead)
    /// statement. We emit it for any such statement where the local may already be dead. We
    /// guarantee to have inserted a [`RepackOp::StorageDead`] before this Op so that one can
    /// safely ignore the statement this is attached to.
    IgnoreStorageDead(Local),
    /// Instructs that the current capability to the place (first [`CapabilityKind`]) should
    /// be weakened to the second given capability. We guarantee that `_.1 > _.2`.
    ///
    /// This Op is used prior to a [`RepackOp::Collapse`] to ensure that all packed up places have
    /// the same capability. It can also appear at basic block join points, where one branch has
    /// a weaker capability than the other.
    Weaken(Place<'tcx>, CapabilityKind, CapabilityKind),
    /// Instructs that one should unpack the first place with the capability.
    /// We guarantee that the current state holds exactly the given capability for the given place.
    /// The second place is the guide, denoting e.g. the enum variant to unpack to. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places (except as noted in the documentation for that fn) which will be obtained by unpacking.
    ///
    /// Until rust-lang/rust#21232 lands, we guarantee that this will only have
    /// [`CapabilityKind::Exclusive`].
    Expand(Place<'tcx>, Place<'tcx>, CapabilityKind),
    /// Instructs that one should pack up to the given (first) place with the given capability.
    /// The second place is the guide, denoting e.g. the enum variant to pack from. One can use
    /// [`Place::expand_one_level(_.0, _.1, ..)`](Place::expand_one_level) to get the set of all
    /// places which should be packed up. We guarantee that the current state holds exactly the
    /// given capability for all places in this set.
    Collapse(Place<'tcx>, Place<'tcx>, CapabilityKind),
    /// TODO
    DerefShallowInit(Place<'tcx>, Place<'tcx>),
}

impl Display for RepackOp<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            RepackOp::StorageDead(place) => write!(f, "StorageDead({place:?})"),
            RepackOp::IgnoreStorageDead(_) => write!(f, "IgnoreSD"),
            RepackOp::Weaken(place, _, to) => {
                write!(f, "Weaken({place:?}, {to:?})")
            }
            RepackOp::Collapse(to, _, kind) => write!(f, "CollapseTo({to:?}, {kind:?})"),
            RepackOp::Expand(from, _, kind) => write!(f, "Expand({from:?}, {kind:?})"),
            RepackOp::DerefShallowInit(from, _) => write!(f, "DerefShallowInit({from:?})"),
        }
    }
}
