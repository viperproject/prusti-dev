// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::iter::FromIterator;
use uuid::Uuid;
use crate::legacy::ast::*;

pub(super) const RETURN_LABEL: &str = "end_of_method";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CfgMethod {
    // TODO: extract logic using (most) skipped fields to CfgMethodBuilder
    #[serde(skip)]
    pub(super) uuid: Uuid,
    pub(super) method_name: String,
    pub(in super::super) formal_arg_count: usize,
    pub(in super::super) formal_returns: Vec<LocalVar>,
    // FIXME: This should be pub(in super::super). However, the optimization
    // that depends on snapshots needs to modify this field.
    pub local_vars: Vec<LocalVar>,
    pub(super) labels: HashSet<String>,
    #[serde(skip)]
    pub(super) reserved_labels: HashSet<String>,
    pub basic_blocks: Vec<CfgBlock>, // FIXME: Hack, should be pub(super).
    pub(super) basic_blocks_labels: Vec<String>,
    #[serde(skip)]
    fresh_var_index: i32,
    #[serde(skip)]
    fresh_label_index: i32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CfgBlock {
    pub stmts: Vec<Stmt>, // FIXME: Hack, should be pub(super).
    pub(in super::super) successor: Successor,
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Successor {
    Undefined,
    Return,
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr, CfgBlockIndex)>, CfgBlockIndex),
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Serialize, Deserialize)]
pub struct CfgBlockIndex {
    #[serde(skip)]
    pub(super) method_uuid: Uuid,
    pub(in super::super) block_index: usize,
}

impl fmt::Debug for CfgBlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cfg:{}", self.block_index)
    }
}
