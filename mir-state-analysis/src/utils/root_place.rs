// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};

use super::{mutable::LocalMutationIsAllowed, Place};

#[derive(Debug, Clone, Copy, Deref, DerefMut)]
pub struct RootPlace<'tcx> {
    #[deref]
    #[deref_mut]
    pub(super) place: Place<'tcx>,
    pub is_local_mutation_allowed: LocalMutationIsAllowed,
}
