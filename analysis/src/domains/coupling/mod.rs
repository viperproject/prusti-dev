// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod analysis;
mod state;
mod graphviz;
mod facts;

use std::collections::BTreeSet;

pub use self::analysis::*;
pub use facts::*;
pub use graphviz::*;
pub use state::*;

pub type FactResult<T> = std::result::Result<T, FactError>;

pub enum FactError {
    /// Internal error: invalid interpretation of the MIR
    MirError(String),
}

/// Helper: Replace a node in a BTreeSet
fn btree_replace<T: Ord>(btree: &mut BTreeSet<T>, from: &T, to: T) {
    if btree.remove(from) {
        btree.insert(to);
    }
}
