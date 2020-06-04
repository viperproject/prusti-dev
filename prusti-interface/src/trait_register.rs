// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use syntax::{ast,ptr};

pub struct TraitRegister {
}

impl TraitRegister {
    pub fn new() -> Self {
        Self {  }
    }

    pub fn register_struct(&self, item: &ptr::P<ast::Item>) {
    }

    pub fn register_trait_decl(&self, item: &ptr::P<ast::Item>) {
        // TODO(@jakob): strip bounds
    }

    pub fn register_impl(&self, item: &ptr::P<ast::Item>) {
        // TODO(@jakob): strip bounds
    }
}
