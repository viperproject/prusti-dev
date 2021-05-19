// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::*;

#[derive(Debug, Clone)]
pub struct Domain {
    pub name: String,
    pub functions: Vec<DomainFunc>,
    pub axioms: Vec<DomainAxiom>,
    pub type_vars: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct DomainFunc {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub unique: bool,
    pub domain_name: String,
}

#[derive(Debug, Clone)]
pub struct DomainAxiom {
    pub name: String,
    pub expr: Expr,
    pub domain_name: String,
}
