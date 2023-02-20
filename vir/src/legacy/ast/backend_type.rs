// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{common::identifier::WithIdentifier, legacy::ast::*};
use std::{collections::BTreeMap, fmt};

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BackendType {
    pub name: String,
    pub functions: Vec<BackendFuncDecl>,
    pub interpretations: BTreeMap<String, String>,
}

impl WithIdentifier for BackendType {
    fn get_identifier(&self) -> String {
        self.name.clone()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct BackendFuncDecl {
    pub name: String,
    pub formal_args: Vec<LocalVar>,
    pub return_type: Type,
    pub domain_name: String,
    pub interpretation: String,
}

impl WithIdentifier for BackendFuncDecl {
    fn get_identifier(&self) -> String {
        // The functions in `low` should be already monomorphised.
        self.name.clone()
    }
}
