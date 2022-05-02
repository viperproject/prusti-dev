// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides utility functions for MIR.

mod all_places;
mod args_for_mir;
mod real_edges;
mod slice_or_array_ref;
mod split_aggregate_assignment;
mod statement_as_assign;
mod statement_at;
mod tuple_items_for_ty;
mod ty_as_ty_ref;
mod mir_place;

pub use self::all_places::*;
pub use self::args_for_mir::*;
pub use self::real_edges::*;
pub use self::slice_or_array_ref::*;
pub use self::split_aggregate_assignment::*;
pub use self::statement_as_assign::*;
pub use self::statement_at::*;
pub use self::tuple_items_for_ty::*;
pub use self::ty_as_ty_ref::*;
pub use self::mir_place::*;
