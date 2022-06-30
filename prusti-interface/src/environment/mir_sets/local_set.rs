// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{data_structures::fx::FxHashSet, middle::mir};

/// A set of MIR places.
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct LocalSet {
    locals: FxHashSet<mir::Local>,
}

impl LocalSet {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn contains_prefix_of(&self, place: mir::Place) -> bool {
        self.locals.contains(&place.local)
    }
    pub fn iter(&self) -> impl Iterator<Item = &mir::Local> {
        self.locals.iter()
    }
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> impl Iterator<Item = mir::Local> {
        self.locals.into_iter()
    }
}

impl From<FxHashSet<mir::Local>> for LocalSet {
    fn from(locals: FxHashSet<mir::Local>) -> Self {
        Self { locals }
    }
}
