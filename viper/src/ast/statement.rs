// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::{
        ast::{self, Declaration, Exp, Field, Position, Stmt},
        plugin::standard::refute,
    },
    scala::collection::immutable::Seq,
};
use super::{no_position, no_trafos, no_info};
use duchess::{IntoJava, JavaConstructor};
use duchess::java::lang::String as JavaString;

pub fn new_stmt(
    lhs: impl IntoJava<Exp>, fields: impl IntoJava<Seq<Field>>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::NewStmt,
        lhs,
        fields
    )
}

pub fn abstract_assign(
    lhs: impl IntoJava<Exp>, rhs: impl IntoJava<Exp>,
) -> impl JavaConstructor<Stmt> {
    ast::AbstractAssign__::get_module().apply(
        lhs,
        rhs,
        no_position(),
        no_info(),
        no_trafos(),
    )
}

pub fn local_var_assign(
    lhs: impl IntoJava<Exp>, rhs: impl IntoJava<Exp>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::LocalVarAssign,
        lhs,
        rhs
    )
}

pub fn field_assign(
    lhs: impl IntoJava<Exp>, rhs: impl IntoJava<Exp>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::FieldAssign,
        lhs,
        rhs
    )
}

pub fn method_call(
    method_name: impl IntoJava<JavaString>, args: impl IntoJava<Seq<Exp>>,
    targets: impl IntoJava<Seq<Exp>>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::MethodCall,
        method_name,
        args,
        targets
    )
}

pub fn method_call_with_pos(
    method_name: impl IntoJava<JavaString>,
    args: impl IntoJava<Seq<Exp>>,
    targets: impl IntoJava<Seq<Exp>>,
    pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node_with_pos!(
        ast::MethodCall,
        method_name,
        args,
        targets,
        pos
    )
}

pub fn exhale(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Exhale::new(
        expr,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn exhale_with_comment(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>, comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    ast::Exhale::new(
        expr,
        pos,
        super::simple_info(&[comment, ""]),
        no_trafos(),
    )
}

pub fn inhale(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Inhale::new(
        expr,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn inhale_with_comment(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>, comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    ast::Inhale::new(
        expr,
        pos,
        super::simple_info(&[comment, ""]),
        no_trafos(),
    )
}

pub fn assert(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Assert::new(
        expr,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn refute(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    refute::Refute::new(
        expr,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn assert_with_comment(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>, comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    ast::Assert::new(
        expr,
        pos,
        super::simple_info(&[comment, ""]),
        no_trafos(),
    )
}

pub fn refute_with_comment(
    expr: impl IntoJava<Exp>, pos: impl IntoJava<Position>, comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    refute::Refute::new(
        expr,
        pos,
        super::simple_info(&[comment, ""]),
        no_trafos(),
    )
}

pub fn fold(
    acc: impl IntoJava<Exp>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(ast::Fold, acc)
}

pub fn fold_with_pos(
    acc: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Fold::new(
        acc,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn unfold(
    acc: impl IntoJava<Exp>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(ast::Unfold, acc)
}

pub fn unfold_with_pos(
    acc: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Unfold::new(
        acc,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn package(
    wand: impl IntoJava<Exp>, proof_script: impl IntoJava<Stmt>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Package::new(
        wand,
        proof_script,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn apply(
    wand: impl IntoJava<Exp>, pos: impl IntoJava<Position>,
) -> impl JavaConstructor<Stmt> {
    ast::Apply::new(
        wand,
        pos,
        no_info(),
        no_trafos(),
    )
}

pub fn seqn(
    stmts: impl IntoJava<Seq<Stmt>>, scoped_decls: impl IntoJava<Seq<Declaration>>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::Seqn,
        stmts,
        scoped_decls
    )
}

pub fn comment(
    comment: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    ast::Seqn::new(
        &[],
        &[],
        no_position(),
        super::simple_info(&[comment]),
        no_trafos(),
    )
}

pub fn if_stmt(
    cond: impl IntoJava<Exp>, then_body: impl IntoJava<Stmt>, else_body: impl IntoJava<Stmt>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::If,
        cond,
        then_body,
        else_body
    )
}

pub fn while_stmt(
    cond: impl IntoJava<Exp>, invs: impl IntoJava<Seq<Exp>>, body: impl IntoJava<Stmt>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::While,
        cond,
        invs,
        body
    )
}

pub fn label(
    name: impl IntoJava<JavaString>, invs: impl IntoJava<Seq<Exp>>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(
        ast::Label,
        name,
        invs
    )
}

pub fn goto(
    target: impl IntoJava<JavaString>,
) -> impl JavaConstructor<Stmt> {
    new_ast_node!(ast::Goto, target)
}
