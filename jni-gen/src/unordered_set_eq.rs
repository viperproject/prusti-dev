// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_hash::FxHashSet;
use std::hash::Hash;

#[derive(Debug, Copy, Clone)]
pub struct UnorderedSetEq<'a, T: 'a>(pub &'a [T]);

impl<'a, T> PartialEq for UnorderedSetEq<'a, T>
where
    T: Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        let a: FxHashSet<_> = self.0.iter().collect();
        let b: FxHashSet<_> = other.0.iter().collect();

        a == b
    }
}
