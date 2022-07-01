// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides utility functions for MIR.

mod all_places;
mod args_for_mir;
mod mir_place;
mod real_edges;
mod slice_or_array_ref;
mod split_aggregate_assignment;
mod statement_as_assign;
mod statement_at;
mod tuple_items_for_ty;
mod ty_as_ty_ref;

pub use self::{
    all_places::*, args_for_mir::*, mir_place::*, real_edges::*, slice_or_array_ref::*,
    split_aggregate_assignment::*, statement_as_assign::*, statement_at::*, tuple_items_for_ty::*,
    ty_as_ty_ref::*,
};
