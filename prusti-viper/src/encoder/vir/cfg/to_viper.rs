// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::cfg::method::*;
use encoder::vir::ast::Position;
use encoder::vir::to_viper::{ToViper, ToViperDecl};
use prusti_interface::config;
use viper;
use viper::AstFactory;

impl<'v> ToViper<'v, viper::Method<'v>> for CfgMethod {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Method<'v> {
        (&self).to_viper(ast)
    }
}

impl<'a, 'v> ToViper<'v, viper::Method<'v>> for &'a CfgMethod {
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

        // Sort blocks by label, except for the first block
        let mut blocks: Vec<_> = self.basic_blocks.iter().enumerate().skip(1).collect();
        blocks.sort_by_key(|(index, _)| index_to_label(&self.basic_blocks_labels, *index));
        blocks.insert(0, (0, &self.basic_blocks[0]));

        for (index, block) in blocks.into_iter() {
            blocks_ast.push(block_to_viper(ast, &self.basic_blocks_labels, block, index));
            declarations.push(
                ast.label(&index_to_label(&self.basic_blocks_labels, index), &[])
                    .into(),
            );
        }
        blocks_ast.push(ast.label(RETURN_LABEL, &[]));
        declarations.push(ast.label(RETURN_LABEL, &[]).into());

        let method_body = Some(ast.seqn(&blocks_ast, &declarations));

        let mut formal_returns_decl: Vec<viper::LocalVarDecl> = vec![];
        for local_var in &self.formal_returns {
            formal_returns_decl.push(local_var.to_viper_decl(ast));
        }

        let method = ast.method(
            &self.method_name,
            &[],
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

fn successor_to_viper<'a>(
    ast: &'a AstFactory,
    index: usize,
    basic_block_labels: &Vec<String>,
    successor: &Successor,
) -> viper::Stmt<'a> {
    match *successor {
        Successor::Undefined => panic!(
            "CFG block '{}' has no successor.",
            basic_block_labels[index].clone()
        ),
        Successor::Return => ast.goto(RETURN_LABEL),
        Successor::BackEdge(target) => {
            if config::use_assume_false_back_edges() {
                let fake_position = Position::new(0, 0, "back edge".to_string());
                ast.seqn(
                    &vec![
                        ast.inhale(
                            ast.false_lit_with_pos(fake_position.to_viper(ast)),
                            fake_position.to_viper(ast)
                        ),
                        ast.goto(RETURN_LABEL),
                    ],
                    &[],
                )
            } else {
                ast.goto(&basic_block_labels[target.block_index])
            }
        }
        Successor::Goto(target) => ast.goto(&basic_block_labels[target.block_index]),
        Successor::GotoSwitch(ref successors, ref default_target) => {
            let mut stmts: Vec<viper::Stmt<'a>> = vec![];
            for (test, target) in successors {
                let goto = ast.goto(&basic_block_labels[target.block_index]);
                let skip = ast.seqn(&[], &[]);
                let conditional_goto = ast.if_stmt(test.to_viper(ast), goto, skip);
                stmts.push(conditional_goto);
            }
            let default_goto = ast.goto(&basic_block_labels[default_target.block_index]);
            stmts.push(default_goto);
            ast.seqn(&stmts, &[])
        }
    }
}

fn block_to_viper<'a>(
    ast: &'a AstFactory,
    basic_block_labels: &Vec<String>,
    block: &CfgBlock,
    index: usize,
) -> viper::Stmt<'a> {
    let label = &basic_block_labels[index];
    let mut stmts: Vec<viper::Stmt> = vec![];
    stmts.push(ast.label(label, &block.invs.to_viper(ast)));
    stmts.extend(block.stmts.to_viper(ast));
    stmts.push(successor_to_viper(
        ast,
        index,
        basic_block_labels,
        &block.successor,
    ));
    ast.seqn(&stmts, &[])
}
