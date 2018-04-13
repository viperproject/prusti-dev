// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ast_factory::*;
use errors::Result as LocalResult;
use uuid::Uuid;

const RETURN_LABEL: &str = "end_of_method";

pub struct CfgMethod<'a: 'b, 'b> {
    ast_factory: &'b AstFactory<'a>,
    uuid: Uuid,
    method_name: String,
    formal_args: Vec<(String, Type<'a>)>,
    formal_returns: Vec<(String, Type<'a>)>,
    local_vars: Vec<(String, Type<'a>)>,
    labels: Vec<String>,
    basic_blocks: Vec<CfgBlock<'a>>,
    basic_blocks_labels: Vec<String>,
    fresh_var_index: i32,
    fresh_label_index: i32,
}

#[derive(Clone)]
struct CfgBlock<'a> {
    invs: Vec<Expr<'a>>,
    stmts: Vec<Stmt<'a>>,
    successor: Successor<'a>,
}

#[derive(Clone)]
pub enum Successor<'a> {
    Undefined,
    Unreachable,
    Return,
    Goto(CfgBlockIndex),
    GotoSwitch(Vec<(Expr<'a>, CfgBlockIndex)>, CfgBlockIndex),
    GotoIf(Expr<'a>, CfgBlockIndex, CfgBlockIndex),
}

#[derive(Clone, Copy)]
pub struct CfgBlockIndex {
    method_uuid: Uuid,
    block_index: usize,
}

impl<'a: 'b, 'b> CfgMethod<'a, 'b> {
    pub fn new(
        ast_factory: &'b AstFactory<'a>,
        method_name: String,
        formal_args: Vec<(String, Type<'a>)>,
        formal_returns: Vec<(String, Type<'a>)>,
        local_vars: Vec<(String, Type<'a>)>,
    ) -> Self {
        CfgMethod {
            ast_factory,
            uuid: Uuid::new_v4(),
            method_name: method_name,
            formal_args,
            formal_returns,
            local_vars,
            labels: Vec::new(),
            basic_blocks: vec![],
            basic_blocks_labels: vec![],
            fresh_var_index: 0,
            fresh_label_index: 0,
        }
    }

    fn is_fresh_local_name(&self, name: &str) -> bool {
        self.formal_args.iter().all(|x| x.0 != name) &&
        self.formal_returns.iter().all(|x| x.0 != name) &&
        self.local_vars.iter().all(|x| x.0 != name) &&
        self.labels.iter().all(|x| x != name)
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

    pub fn add_fresh_local_var(&mut self, typ: Type<'a>) -> String {
        let name = self.generate_fresh_local_var_name();
        self.local_vars.push((name.clone(), typ));
        name
    }

    pub fn add_fresh_formal_arg(&mut self, typ: Type<'a>) -> String {
        let name = self.generate_fresh_local_var_name();
        self.formal_args.push((name.clone(), typ));
        name
    }

    pub fn add_fresh_formal_return(&mut self, typ: Type<'a>) -> String {
        let name = self.generate_fresh_local_var_name();
        self.formal_returns.push((name.clone(), typ));
        name
    }

    pub fn add_local_var(&mut self, name: &str, typ: Type<'a>) {
        assert!(self.is_fresh_local_name(name));
        self.local_vars.push((name.to_string(), typ));
    }

    pub fn add_formal_arg(&mut self, name: &str, typ: Type<'a>) {
        assert!(self.is_fresh_local_name(name));
        self.formal_args.push((name.to_string(), typ));
    }

    pub fn add_formal_return(&mut self, name: &str, typ: Type<'a>) {
        assert!(self.is_fresh_local_name(name));
        self.formal_returns.push((name.to_string(), typ));
    }

    pub fn add_stmt(&mut self, index: CfgBlockIndex, stmt: Stmt<'a>) {
        self.basic_blocks[index.block_index].stmts.push(stmt);
    }

    pub fn add_label_stmt(&mut self, index: CfgBlockIndex, label: &str) {
        assert!(self.is_fresh_local_name(label));
        let stmt = self.ast_factory.label(label, &[]);
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

    pub fn add_block(&mut self, label: &str, invs: Vec<Expr<'a>>, stmts: Vec<Stmt<'a>>) -> CfgBlockIndex {
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

    pub fn set_successor(&mut self, index: CfgBlockIndex, successor: Successor<'a>) {
        assert_eq!(
            self.uuid, index.method_uuid,
            "The provided CfgBlockIndex doesn't belong to this CfgMethod"
        );
        self.basic_blocks[index.block_index].successor = successor;
    }

    #[cfg_attr(feature = "cargo-clippy", allow(wrong_self_convention))]
    pub fn to_ast(self) -> LocalResult<Method<'a>> {
        let mut blocks_ast: Vec<Stmt> = vec![];
        let mut declarations: Vec<Declaration> = vec![];

        for &(ref name, ref typ) in self.local_vars.iter() {
            let decl = self.ast_factory.local_var_decl(name, *typ);
            declarations.push(decl.into());
        }
        for label in self.labels.iter() {
            let decl = self.ast_factory.label(label, &[]);
            declarations.push(decl.into());
        }

        for (index, block) in self.basic_blocks.iter().enumerate() {
            blocks_ast.push(block_to_ast(
                self.ast_factory,
                &self.basic_blocks_labels,
                block,
                index,
            ));
            declarations.push(
                self.ast_factory
                    .label(&index_to_label(&self.basic_blocks_labels, index), &[])
                    .into(),
            );
        }
        blocks_ast.push(
            self.ast_factory
                .label(&return_label(), &[]),
        );
        declarations.push(
            self.ast_factory
                .label(&return_label(), &[])
                .into(),
        );

        let method_body = Some(self.ast_factory.seqn(&blocks_ast, &declarations));

        let mut formal_args_decl: Vec<LocalVarDecl<'a>> = vec![];
        for &(ref name, ref typ) in &self.formal_args {
            let decl = self.ast_factory.local_var_decl(name, *typ);
            formal_args_decl.push(decl);
        }

        let mut formal_returns_decl: Vec<LocalVarDecl<'a>> = vec![];
        for &(ref name, ref typ) in &self.formal_returns {
            let decl = self.ast_factory.local_var_decl(name, *typ);
            formal_returns_decl.push(decl);
        }

        let method = self.ast_factory.method(
            &self.method_name,
            &formal_args_decl,
            &formal_returns_decl,
            &[],
            &[],
            method_body,
        );

        Ok(method)
    }
}

fn index_to_label(basic_block_labels: &Vec<String>, index: usize) -> String {
    basic_block_labels[index].clone()
}

fn return_label() -> String {
    RETURN_LABEL.to_string()
}

fn successor_to_ast<'a>(
    ast: &'a AstFactory,
    index: usize,
    basic_block_labels: &Vec<String>,
    successor: &Successor<'a>,
) -> Stmt<'a> {
    match *successor {
        Successor::Undefined =>
            panic!("CFG block '{}' has no successor.", index_to_label(basic_block_labels, index)),
        Successor::Unreachable =>
            ast.assert(ast.false_lit(), ast.no_position()),
        Successor::Return => ast.goto(&return_label()),
        Successor::Goto(target) => ast.goto(&index_to_label(basic_block_labels, target.block_index)),
        Successor::GotoSwitch(ref successors, ref default_target) => {
            let skip = ast.seqn(&[], &[]);
            let mut stmts: Vec<Stmt> = vec![];
            for &(test, target) in successors {
                let goto = ast.goto(&index_to_label(basic_block_labels, target.block_index));
                let conditional_goto = ast.if_stmt(test, goto, skip);
                stmts.push(conditional_goto);
            }
            let default_goto = ast.goto(&index_to_label(basic_block_labels, default_target.block_index));
            stmts.push(default_goto);
            ast.seqn(&stmts, &[])
        }
        Successor::GotoIf(test, then_target, else_target) => {
            let then_goto = ast.goto(&index_to_label(basic_block_labels, then_target.block_index));
            let else_goto = ast.goto(&index_to_label(basic_block_labels, else_target.block_index));
            ast.if_stmt(test, then_goto, else_goto)
        }
    }
}

fn block_to_ast<'a>(
    ast: &'a AstFactory,
    basic_block_labels: &Vec<String>,
    block: &CfgBlock<'a>,
    index: usize,
) -> Stmt<'a> {
    let label = index_to_label(basic_block_labels, index);
    let mut stmts: Vec<Stmt> = vec![];
    stmts.push(
        ast.label(&label, &block.invs)
    );
    stmts.extend(
        &block.stmts
    );
    stmts.push(
        successor_to_ast(ast, index, basic_block_labels, &block.successor)
    );
    ast.seqn(&stmts, &[])
}
