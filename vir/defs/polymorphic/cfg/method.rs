// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::iter::FromIterator;
use uuid::Uuid;
use crate::polymorphic::ast::*;

use super::super::super::{legacy, converter};

pub(super) const RETURN_LABEL: &str = "end_of_method";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CfgMethod {
    // TODO: extract logic using (most) skipped fields to CfgMethodBuilder
    #[serde(skip)]
    pub(crate) uuid: Uuid,
    pub(crate) method_name: String,
    pub(crate) formal_arg_count: usize,
    pub(crate) formal_returns: Vec<LocalVar>,
    // FIXME: This should be pub(in super::super). However, the optimization
    // that depends on snapshots needs to modify this field.
    pub local_vars: Vec<LocalVar>,
    pub(crate) labels: HashSet<String>,
    #[serde(skip)]
    pub(crate) reserved_labels: HashSet<String>,
    pub basic_blocks: Vec<CfgBlock>, // FIXME: Hack, should be pub(super).
    pub(crate) basic_blocks_labels: Vec<String>,
    #[serde(skip)]
    pub(crate) fresh_var_index: i32,
    #[serde(skip)]
    pub(crate) fresh_label_index: i32,
}

impl CfgMethod {
    pub fn new(
        method_name: String,
        formal_arg_count: usize,
        formal_returns: Vec<LocalVar>,
        local_vars: Vec<LocalVar>,
        reserved_labels: Vec<String>,
    ) -> Self {
        CfgMethod {
            uuid: Uuid::new_v4(),
            method_name,
            formal_arg_count,
            formal_returns,
            local_vars,
            labels: HashSet::new(),
            reserved_labels: HashSet::from_iter(reserved_labels),
            basic_blocks: vec![],
            basic_blocks_labels: vec![],
            fresh_var_index: 0,
            fresh_label_index: 0,
        }
    }
}

impl From<CfgMethod> for legacy::CfgMethod {
    fn from(cfg_method: CfgMethod) -> legacy::CfgMethod {
        legacy::CfgMethod {
            uuid: cfg_method.uuid,
            method_name: cfg_method.method_name.clone(),
            formal_arg_count: cfg_method.formal_arg_count,
            formal_returns: cfg_method.formal_returns.iter().map(|formal_return| legacy::LocalVar::from(formal_return.clone())).collect(),
            local_vars: cfg_method.local_vars.iter().map(|local_var| legacy::LocalVar::from(local_var.clone())).collect(),
            labels: cfg_method.labels.iter().map(|label| label.clone()).collect(),
            reserved_labels: cfg_method.reserved_labels.iter().map(|reserved_label| reserved_label.clone()).collect(),
            basic_blocks: cfg_method.basic_blocks.iter().map(|basic_block| legacy::CfgBlock::from(basic_block.clone())).collect(),
            basic_blocks_labels: cfg_method.basic_blocks_labels.iter().map(|basic_blocks_label| basic_blocks_label.clone()).collect(),
            fresh_var_index: cfg_method.fresh_var_index,
            fresh_label_index: cfg_method.fresh_label_index,
        }
    }
}

impl converter::Generic for CfgMethod {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut cfg_method = self;
        cfg_method.formal_returns = cfg_method.formal_returns.into_iter().map(|formal_return| formal_return.substitute(map)).collect();
        cfg_method.local_vars = cfg_method.local_vars.into_iter().map(|local_var| local_var.substitute(map)).collect();
        cfg_method.basic_blocks = cfg_method.basic_blocks.into_iter().map(|basic_block| basic_block.substitute(map)).collect();
        cfg_method
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CfgBlock {
    pub stmts: Vec<Stmt>, // FIXME: Hack, should be pub(super).
    pub(crate) successor: Successor,
}

impl From<CfgBlock> for legacy::CfgBlock {
    fn from(cfg_block: CfgBlock) -> legacy::CfgBlock {
        legacy::CfgBlock {
            stmts: cfg_block.stmts.iter().map(|stmt| legacy::Stmt::from(stmt.clone())).collect(),
            successor: legacy::Successor::from(cfg_block.successor.clone()),
        }
    }
}

impl converter::Generic for CfgBlock {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        let mut cfg_block = self;
        cfg_block.stmts = cfg_block.stmts.into_iter().map(|stmt| stmt.substitute(map)).collect();
        cfg_block.successor = cfg_block.successor.substitute(map);
        cfg_block
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub enum Successor {
    Undefined,
    Return,
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr, CfgBlockIndex)>, CfgBlockIndex),
}

impl From<Successor> for legacy::Successor {
    fn from(successor: Successor) -> legacy::Successor {
        match successor {
            Successor::Undefined => legacy::Successor::Undefined,
            Successor::Return => legacy::Successor::Return,
            Successor::Goto(cfg_block_index) => legacy::Successor::Goto(legacy::CfgBlockIndex::from(cfg_block_index.clone())),
            Successor::GotoSwitch(expr_indices, cfg_block_index) => legacy::Successor::GotoSwitch(
                expr_indices.iter().map(|(expr, index)| (legacy::Expr::from(expr.clone()), legacy::CfgBlockIndex::from(index.clone()))).collect(),
                legacy::CfgBlockIndex::from(cfg_block_index.clone()),
            ),
        }
    }
}

impl converter::Generic for Successor {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self {
        match self {
            Successor::Undefined | Successor::Return => self,
            Successor::Goto(cfg_block_index) => Successor::Goto(cfg_block_index.substitute(map)),
            Successor::GotoSwitch(expr_indices, cfg_block_index) => Successor::GotoSwitch(
                expr_indices.into_iter().map(|(expr, index)| (expr.substitute(map), index.substitute(map))).collect(),
                cfg_block_index.substitute(map),
            ),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Serialize, Deserialize)]
pub struct CfgBlockIndex {
    #[serde(skip)]
    pub(crate) method_uuid: Uuid,
    pub(crate) block_index: usize,
}

impl fmt::Debug for CfgBlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cfg:{}", self.block_index)
    }
}

impl From<CfgBlockIndex> for legacy::CfgBlockIndex {
    fn from(cfg_block_index: CfgBlockIndex) -> legacy::CfgBlockIndex {
        legacy::CfgBlockIndex {
            method_uuid: cfg_block_index.method_uuid,
            block_index: cfg_block_index.block_index,
        }
    }
}

impl converter::Generic for CfgBlockIndex {
    fn substitute(self, _map: &HashMap<TypeVar, Type>) -> Self {
        self
    }
}
