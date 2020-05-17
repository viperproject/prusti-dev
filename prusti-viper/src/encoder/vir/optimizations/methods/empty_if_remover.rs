// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Optimization that removes unused if statements.

use encoder::vir::cfg;
use encoder::vir::Stmt;

/// Remove empty if statements:
/// * `if (...) {}`
/// * `if (...) { /* ... */ }`
/// * `if (...) { if (...) {}; if (...) { /* ... */ } }`
pub fn remove_empty_if(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    method.retain_stmts(|stmt| {
        match stmt {
            Stmt::If(_, ref stmts) => !is_empty_body(stmts),
            _ => true, // Keep the rest
        }
    });
    method
}

fn is_empty_body(stmts: &Vec<Stmt>) -> bool {
    stmts.iter().all(|stmt| match stmt {
        Stmt::Comment(_) |
        Stmt::TransferPerm(..) => true,
        Stmt::If(_, ref stmts) => is_empty_body(stmts),
        _ => false
    })
}
