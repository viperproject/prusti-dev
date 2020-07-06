// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that contains optimizations for methods.

mod empty_if_remover;
mod assert_remover;
mod var_remover;
mod purifier;

pub use self::empty_if_remover::remove_empty_if;
pub use self::assert_remover::remove_trivial_assertions;
pub use self::var_remover::remove_unused_vars;
pub use self::purifier::purify_vars;
