// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Register containing information on what traits are declared, and what traits are implemented on
/// what types. The register does not consider cross-crate trait implementations, but does consider
/// cross-module implementations.
pub struct TraitRegister {}

impl TraitRegister {
    pub fn new() -> Self {
        TraitRegister { }
    }

    pub fn register_struct(&mut self, type_name: String) {
        warn!("registering struct: {}", type_name);
    }

    pub fn register_trait_decl(&mut self, trait_name: String) {
        warn!("registering trait: {}", trait_name);
    }

    // register trait
    // pulls invariant strings defined on trait declaration

    // register implementation
    // creates a link between type and trait declaration

    // register trait aliases

    // register type aliases

    // register enum declaration

    // register derive?

    // poll type
    // get invariants based on traits for some type

}

