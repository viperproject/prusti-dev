// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! The log keeps track of actions performed by the fold-unfold algorithm so that they can be
//! undone when restoring borrowed permissions.

use encoder::vir;
use encoder::foldunfold::action::Action;
use std::collections::HashMap;

#[derive(Clone)]
pub(super) struct EventLog {
    /// Actions performed by the fold-unfold algorithm before the join. We can use a single
    /// CfgBlockIndex because fold-unfold algorithms generates a new basic block for dropped
    /// permissions.
    prejoin_actions: HashMap<vir::CfgBlockIndex, Vec<Action>>,
}

impl EventLog {
    pub fn new() -> Self {
        Self {
            prejoin_actions: HashMap::new(),
        }
    }
    pub fn log_prejoin_action(&mut self, block_index: vir::CfgBlockIndex, action: Action) {
        let entry = self.prejoin_actions.entry(block_index).or_insert(Vec::new());
        entry.push(action);
    }
}
