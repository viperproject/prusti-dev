// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::ast::*;
use std::collections::HashSet;
use std::fmt;
use std::iter::FromIterator;
use uuid::Uuid;

pub(super) const RETURN_LABEL: &str = "end_of_method";

#[derive(Debug, Clone)]
pub struct CfgMethod {
    pub(super) uuid: Uuid,
    pub(super) method_name: String,
    pub(super) formal_args: Vec<LocalVar>,
    pub(super) formal_returns: Vec<LocalVar>,
    pub(super) local_vars: Vec<LocalVar>,
    pub(super) labels: HashSet<String>,
    pub(super) reserved_labels: HashSet<String>,
    pub(super) basic_blocks: Vec<CfgBlock>,
    pub(super) basic_blocks_labels: Vec<String>,
    fresh_var_index: i32,
    fresh_label_index: i32,
}

#[derive(Debug, Clone)]
pub(super) struct CfgBlock {
    pub(super) invs: Vec<Expr>,
    pub(super) stmts: Vec<Stmt>,
    pub(super) successor: Successor,
}

#[derive(Debug, Clone)]
pub enum Successor {
    Undefined,
    Return,
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr, CfgBlockIndex)>, CfgBlockIndex),
    GotoIf(Expr, CfgBlockIndex, CfgBlockIndex),
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct CfgBlockIndex {
    pub(super) method_uuid: Uuid,
    pub(super) block_index: usize,
}

impl fmt::Debug for CfgBlockIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cfg:{}", self.block_index)
    }
}

impl Successor {
    pub fn get_following(&self) -> Vec<CfgBlockIndex> {
        match self {
            &Successor::Undefined |
            &Successor::Return => vec![],
            &Successor::Goto(target) => vec![
                target
            ],
            &Successor::GotoSwitch(ref guarded_targets, default_target) => {
                let mut res: Vec<CfgBlockIndex> = guarded_targets.iter().map(|g| g.1).collect();
                res.push(default_target);
                res
            },
            &Successor::GotoIf(_, then_target, else_target) => vec![
                then_target,
                else_target
            ],
        }
    }

    pub fn replace_target(self, src: CfgBlockIndex, dst: CfgBlockIndex) -> Self {
        assert_eq!(
            src.method_uuid, dst.method_uuid,
            "The provided src CfgBlockIndex is not compatible with the dst CfgBlockIndex"
        );
        match self {
            Successor::Goto(target) => Successor::Goto(
                if target == src { dst } else { target }
            ),
            Successor::GotoSwitch(guarded_targets, default_target) => Successor::GotoSwitch(
                guarded_targets.into_iter().map(|x| (x.0, if x.1 == src { dst } else { x.1 })).collect(),
                if default_target == src { dst } else { default_target }
            ),
            Successor::GotoIf(expr, then_target, else_target) => Successor::GotoIf(
                expr,
                if then_target == src { dst } else { then_target },
                if else_target == src { dst } else { else_target }
            ),
            x => x
        }
    }

    pub(super) fn replace_uuid(self, new_uuid: Uuid) -> Self {
        match self {
            Successor::Goto(target) => Successor::Goto(
                target.set_uuid(new_uuid)
            ),
            Successor::GotoSwitch(guarded_targets, default_target) => Successor::GotoSwitch(
                guarded_targets.into_iter().map(|x| (x.0, x.1.set_uuid(new_uuid))).collect(),
                default_target.set_uuid(new_uuid)
            ),
            Successor::GotoIf(expr, then_target, else_target) => Successor::GotoIf(
                expr,
                then_target.set_uuid(new_uuid),
                else_target.set_uuid(new_uuid)
            ),
            x => x
        }
    }
}

impl CfgBlockIndex {
    pub(super) fn set_uuid(self, method_uuid: Uuid) -> Self {
        CfgBlockIndex {
            method_uuid,
            ..self
        }
    }
}

impl CfgMethod {
    pub fn new(
        method_name: String,
        formal_args: Vec<LocalVar>,
        formal_returns: Vec<LocalVar>,
        local_vars: Vec<LocalVar>,
        reserved_labels: Vec<String>,
    ) -> Self {
        CfgMethod {
            uuid: Uuid::new_v4(),
            method_name,
            formal_args,
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

    pub fn name(&self) -> String {
        self.method_name.clone()
    }

    pub(super) fn block_index(&self, index: usize) -> CfgBlockIndex {
        CfgBlockIndex {
            method_uuid: self.uuid,
            block_index: index
        }
    }

    fn is_fresh_local_name(&self, name: &str) -> bool {
        self.formal_args.iter().all(|x| x.name != name)
            && self.formal_returns.iter().all(|x| x.name != name)
            && self.local_vars.iter().all(|x| x.name != name)
            && !self.labels.contains(name)
            && self.basic_blocks_labels.iter().all(|x| x != name)
    }

    fn generate_fresh_local_var_name(&mut self) -> String {
        let mut candidate_name = format!("__t{}", self.fresh_var_index);
        self.fresh_var_index += 1;
        while !self.is_fresh_local_name(&candidate_name) || self.reserved_labels.contains(&candidate_name) {
            candidate_name = format!("__t{}", self.fresh_var_index);
            self.fresh_var_index += 1;
        }
        candidate_name
    }

    pub fn get_fresh_label_name(&mut self) -> String {
        let mut candidate_name = format!("l{}", self.fresh_label_index);
        self.fresh_label_index += 1;
        while !self.is_fresh_local_name(&candidate_name) || self.reserved_labels.contains(&candidate_name) {
            candidate_name = format!("l{}", self.fresh_label_index);
            self.fresh_label_index += 1;
        }
        candidate_name
    }

    /// Returns all formal arguments, formal returns, and local variables
    pub fn get_all_vars(&self) -> Vec<LocalVar> {
        let mut vars: Vec<LocalVar> = vec![];
        vars.extend(self.formal_args.clone());
        vars.extend(self.formal_returns.clone());
        vars.extend(self.local_vars.clone());
        vars
    }

    /// Returns all formal returns and local variables
    pub fn get_formal_returns_and_local_vars(&self) -> Vec<LocalVar> {
        let mut vars: Vec<LocalVar> = vec![];
        vars.extend(self.formal_returns.clone());
        vars.extend(self.local_vars.clone());
        vars
    }

    /// Returns all labels
    pub fn get_all_labels(&self) -> Vec<String> {
        let mut labels: Vec<String> = vec![];
        labels.extend(self.labels.iter().cloned());
        labels.extend(self.basic_blocks_labels.iter().cloned());
        labels
    }

    pub fn add_fresh_local_var(&mut self, typ: Type) -> LocalVar {
        let name = self.generate_fresh_local_var_name();
        let local_var = LocalVar::new(name, typ);
        self.local_vars.push(local_var.clone());
        local_var
    }

    pub fn add_fresh_formal_arg(&mut self, typ: Type) -> LocalVar {
        let name = self.generate_fresh_local_var_name();
        let local_var = LocalVar::new(name, typ);
        self.formal_args.push(local_var.clone());
        local_var
    }

    pub fn add_fresh_formal_return(&mut self, typ: Type) -> LocalVar {
        let name = self.generate_fresh_local_var_name();
        let local_var = LocalVar::new(name, typ);
        self.formal_returns.push(local_var.clone());
        local_var
    }

    pub fn add_local_var(&mut self, name: &str, typ: Type) {
        assert!(self.is_fresh_local_name(name));
        self.local_vars.push(LocalVar::new(name, typ));
    }

    pub fn add_formal_arg(&mut self, name: &str, typ: Type) {
        assert!(self.is_fresh_local_name(name));
        self.formal_args.push(LocalVar::new(name, typ));
    }

    pub fn add_formal_return(&mut self, name: &str, typ: Type) {
        assert!(self.is_fresh_local_name(name));
        self.formal_returns.push(LocalVar::new(name, typ));
    }

    pub fn add_stmt(&mut self, index: CfgBlockIndex, stmt: Stmt) {
        if let &Stmt::Label(ref label_name) = &stmt {
            assert!(self.is_fresh_local_name(label_name), "label {} is not fresh", label_name);
            self.labels.insert(label_name.clone());
        };
        self.basic_blocks[index.block_index].stmts.push(stmt);
    }

    pub fn add_block(&mut self, label: &str, invs: Vec<Expr>, stmts: Vec<Stmt>) -> CfgBlockIndex {
        assert!(label.chars().take(1).all(|c| c.is_alphabetic() || c == '_'));
        assert!(label.chars().skip(1).all(|c| c.is_alphanumeric() || c == '_'));
        assert!(self.basic_blocks_labels.iter().all(|l| l != label));
        assert!(label != RETURN_LABEL);
        let index = self.basic_blocks.len();
        self.basic_blocks_labels.push(label.to_string());
        self.basic_blocks.push(CfgBlock {
            invs,
            stmts,
            successor: Successor::Undefined,
        });
        self.block_index(index)
    }

    pub fn set_successor(&mut self, index: CfgBlockIndex, successor: Successor) {
        assert_eq!(
            self.uuid, index.method_uuid,
            "The provided CfgBlockIndex doesn't belong to this CfgMethod"
        );
        self.basic_blocks[index.block_index].successor = successor;
    }

    pub fn get_preceding(&self, target_index: CfgBlockIndex) -> Vec<CfgBlockIndex> {
        assert_eq!(
            self.uuid, target_index.method_uuid,
            "The provided CfgBlockIndex doesn't belong to this CfgMethod"
        );
        self.basic_blocks
            .iter()
            .enumerate()
            .filter(
                |x| x.1.successor.get_following().contains(&target_index)
            ).map(
                |x| self.block_index(x.0)
            ).collect()
    }

    pub fn get_initial_block(&self) -> CfgBlockIndex {
        self.block_index(0)
    }

    pub fn get_topological_sort(&self) -> Vec<CfgBlockIndex> {
        let mut visited: Vec<bool> = vec![false; self.basic_blocks.len()];
        let mut topo_sorted: Vec<CfgBlockIndex> = vec![];

        for index in 0..self.basic_blocks.len() {
            if !visited[index] {
                self.topological_sort_impl(&mut visited, &mut topo_sorted, index);
            }
        }

        topo_sorted.into_iter().rev().collect()
    }

    fn topological_sort_impl(&self, visited: &mut Vec<bool>, topo_sorted: &mut Vec<CfgBlockIndex>, curr_index: usize) {
        assert!(!visited[curr_index]);
        visited[curr_index] = true;
        let curr_block = &self.basic_blocks[curr_index];
        let following = curr_block.successor.get_following();

        for block_index in following {
            let index = block_index.block_index;
            if !visited[index] {
                self.topological_sort_impl(visited, topo_sorted, index);
            }
        }

        topo_sorted.push(self.block_index(curr_index))
    }
}
