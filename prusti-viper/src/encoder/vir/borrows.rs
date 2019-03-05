// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ReborrowingDAG {
}

impl ReborrowingDAG {
    pub fn new() -> Self {
        Self {}
    }
}

impl fmt::Debug for ReborrowingDAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG")
    }
}

impl fmt::Display for ReborrowingDAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG")
    }
}
