// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper;
use viper::AstFactory;
use uuid::Uuid;
use encoder::vir::ast::*;
use encoder::vir::to_viper::{ToViper, ToViperDecl};

const RETURN_LABEL: &str = "end_of_method";

#[derive(Debug, Clone)]
pub struct CfgMethod {
    uuid: Uuid,
    method_name: String,
    formal_args: Vec<LocalVar>,
    formal_returns: Vec<LocalVar>,
    local_vars: Vec<LocalVar>,
    labels: Vec<String>,
    basic_blocks: Vec<CfgBlock>,
    basic_blocks_labels: Vec<String>,
    fresh_var_index: i32,
    fresh_label_index: i32,
}

#[derive(Debug, Clone)]
struct CfgBlock {
    invs: Vec<Expr>,
    stmts: Vec<Stmt>,
    successor: Successor,
}

#[derive(Debug, Clone)]
pub enum Successor {
    Undefined,
    Unreachable,
    Return,
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr, CfgBlockIndex)>, CfgBlockIndex),
    GotoIf(Expr, CfgBlockIndex, CfgBlockIndex),
}

#[derive(Debug, Clone, Copy)]
pub struct CfgBlockIndex {
    method_uuid: Uuid,
    block_index: usize,
}

impl CfgMethod {
    pub fn new(
        method_name: String,
        formal_args: Vec<LocalVar>,
        formal_returns: Vec<LocalVar>,
        local_vars: Vec<LocalVar>,
    ) -> Self {
        CfgMethod {
            uuid: Uuid::new_v4(),
            method_name: method_name,
            formal_args,
            formal_returns,
            local_vars,
            labels: vec![],
            basic_blocks: vec![],
            basic_blocks_labels: vec![],
            fresh_var_index: 0,
            fresh_label_index: 0,
        }
    }

    fn is_fresh_local_name(&self, name: &str) -> bool {
        self.formal_args.iter().all(|x| x.name != name)
            && self.formal_returns.iter().all(|x| x.name != name)
            && self.local_vars.iter().all(|x| x.name != name)
            && self.labels.iter().all(|x| x != name)
    }

    fn generate_fresh_local_var_name(&mut self) -> String {
        let mut candidate_name = format!("__{}", self.fresh_var_index);
        self.fresh_var_index += 1;
        while !self.is_fresh_local_name(&candidate_name) {
            candidate_name = format!("__{}", self.fresh_var_index);
            self.fresh_var_index += 1;
        }
        candidate_name
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
        self.basic_blocks[index.block_index].stmts.push(stmt);
    }

    pub fn add_label_stmt(&mut self, index: CfgBlockIndex, label: &str) {
        assert!(self.is_fresh_local_name(label));
        let stmt = Stmt::Label(label.to_string());
        self.labels.push(label.to_string());
        self.basic_blocks[index.block_index].stmts.push(stmt);
    }

    pub fn get_fresh_label_name(&mut self) -> String {
        let mut candidate_name = format!("l{}", self.fresh_label_index);
        self.fresh_label_index += 1;
        while !self.is_fresh_local_name(&candidate_name) {
            candidate_name = format!("l{}", self.fresh_label_index);
            self.fresh_label_index += 1;
        }
        self.labels.push(candidate_name.clone());
        candidate_name
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
        CfgBlockIndex {
            method_uuid: self.uuid,
            block_index: index,
        }
    }

    pub fn set_successor(&mut self, index: CfgBlockIndex, successor: Successor) {
        assert_eq!(
            self.uuid, index.method_uuid,
            "The provided CfgBlockIndex doesn't belong to this CfgMethod"
        );
        self.basic_blocks[index.block_index].successor = successor;
    }
}

impl<'v> ToViper<'v, viper::Method<'v>> for CfgMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        let mut blocks_ast: Vec<viper::Stmt> = vec![];
        let mut declarations: Vec<viper::Declaration> = vec![];

        for local_var in self.local_vars.iter() {
            declarations.push(local_var.to_viper_decl(ast).into());
        }
        for label in self.labels.iter() {
            let decl = ast.label(label, &[]);
            declarations.push(decl.into());
        }

        for (index, block) in self.basic_blocks.iter().enumerate() {
            blocks_ast.push(block_to_ast(
                ast,
                &self.basic_blocks_labels,
                block,
                index,
            ));
            declarations.push(
                ast
                    .label(&index_to_label(&self.basic_blocks_labels, index), &[])
                    .into(),
            );
        }
        blocks_ast.push(
            ast
                .label(RETURN_LABEL, &[]),
        );
        declarations.push(
            ast
                .label(RETURN_LABEL, &[])
                .into(),
        );

        let method_body = Some(ast.seqn(&blocks_ast, &declarations));

        let mut formal_args_decl: Vec<viper::LocalVarDecl> = vec![];
        for local_var in &self.formal_args {
            formal_args_decl.push(local_var.to_viper_decl(ast));
        }

        let mut formal_returns_decl: Vec<viper::LocalVarDecl> = vec![];
        for local_var in &self.formal_returns {
            formal_returns_decl.push(local_var.to_viper_decl(ast));
        }

        let method = ast.method(
            &self.method_name,
            &formal_args_decl,
            &formal_returns_decl,
            &[],
            &[],
            method_body,
        );

        method
    }
}

impl<'v> ToViper<'v, Vec<viper::Method<'v>>> for Vec<CfgMethod> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Method<'v>> {
        self.iter().map(|x| x.to_viper(ast)).collect()
    }
}

fn index_to_label(basic_block_labels: &Vec<String>, index: usize) -> String {
    basic_block_labels[index].clone()
}

fn successor_to_ast<'a>(
    ast: &'a AstFactory,
    index: usize,
    basic_block_labels: &Vec<String>,
    successor: &Successor,
) -> viper::Stmt<'a> {
    match *successor {
        Successor::Undefined =>
            panic!("CFG block '{}' has no successor.", basic_block_labels[index].clone()),
        Successor::Unreachable =>
            ast.assert(ast.false_lit(), ast.no_position()),
        Successor::Return => ast.goto(RETURN_LABEL),
        Successor::Goto(target) => ast.goto(&basic_block_labels[target.block_index]),
        Successor::GotoSwitch(ref successors, ref default_target) => {
            let skip = ast.seqn(&[], &[]);
            let mut stmts: Vec<viper::Stmt<'a>> = vec![];
            for (test, target) in successors {
                let goto = ast.goto(&basic_block_labels[target.block_index]);
                let conditional_goto = ast.if_stmt(test.to_viper(ast), goto, skip);
                stmts.push(conditional_goto);
            }
            let default_goto = ast.goto(&basic_block_labels[default_target.block_index]);
            stmts.push(default_goto);
            ast.seqn(&stmts, &[])
        }
        Successor::GotoIf(ref test, then_target, else_target) => {
            let then_goto = ast.goto(&basic_block_labels[then_target.block_index]);
            let else_goto = ast.goto(&basic_block_labels[else_target.block_index]);
            ast.if_stmt(test.to_viper(ast), then_goto, else_goto)
        }
    }
}

fn block_to_ast<'a>(
    ast: &'a AstFactory,
    basic_block_labels: &Vec<String>,
    block: &CfgBlock,
    index: usize,
) -> viper::Stmt<'a> {
    let label = &basic_block_labels[index];
    let mut stmts: Vec<viper::Stmt> = vec![];
    stmts.push(
        ast.label(label, &block.invs.to_viper(ast))
    );
    stmts.extend(
        &block.stmts.to_viper(ast)
    );
    stmts.push(
        successor_to_ast(ast, index, basic_block_labels, &block.successor)
    );
    ast.seqn(&stmts, &[])
}
