// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Expr;
use ast_factory::structs::Field;
use ast_factory::structs::Position;
use ast_factory::structs::Stmt;
use ast_factory::structs::Declaration;
use jni::objects::JObject;

impl<'a> AstFactory<'a> {
    pub fn new_stmt(&self, lhs: Expr, fields: &[Field]) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::NewStmt,
            lhs.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(fields))
        )
    }

    pub fn abstract_assign(&self, lhs: Expr, rhs: Expr) -> Stmt<'a> {
        let abstract_assign_wrapper = ast::AbstractAssign_object::with(self.env);
        let abstract_assign_instance = self.jni.unwrap_result(
            abstract_assign_wrapper.singleton()
        );
        let obj = self.jni.unwrap_result(abstract_assign_wrapper.call_apply(
            abstract_assign_instance,
            lhs.to_jobject(),
            rhs.to_jobject(),
            self.no_position().to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn local_var_assign(&self, lhs: Expr, rhs: Expr) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::LocalVarAssign,
            lhs.to_jobject(),
            rhs.to_jobject()
        )
    }

    pub fn field_assign(&self, lhs: Expr, rhs: Expr) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::FieldAssign,
            lhs.to_jobject(),
            rhs.to_jobject()
        )
    }

    pub fn method_call(&self, method_name: &str, args: &[Expr], targets: &[Expr]) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::MethodCall,
            self.jni.new_string(method_name),
            self.jni.new_seq(&map_to_jobjects!(args)),
            self.jni.new_seq(&map_to_jobjects!(targets))
        )
    }

    pub fn exhale(&self, expr: Expr, pos: Position) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Exhale::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn exhale_with_comment(&self, expr: Expr, pos: Position, comment: &str) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Exhale::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.simple_info(&[comment, ""]),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn inhale(&self, expr: Expr, pos: Position) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Inhale::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn inhale_with_comment(&self, expr: Expr, pos: Position, comment: &str) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Inhale::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.simple_info(&[comment, ""]),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn assert(&self, expr: Expr, pos: Position) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.no_info(),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn assert_with_comment(&self, expr: Expr, pos: Position, comment: &str) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.simple_info(&[comment, ""]),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn fold(&self, acc: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Fold, acc.to_jobject())
    }

    pub fn unfold(&self, acc: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Unfold, acc.to_jobject())
    }

    pub fn package(&self, wand: Expr, proof_script: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Package,
            wand.to_jobject(),
            proof_script.to_jobject()
        )
    }

    pub fn apply(&self, wand: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Apply, wand.to_jobject())
    }

    pub fn seqn(&self, stmts: &[Stmt], scoped_decls: &[Declaration]) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Seqn,
            self.jni.new_seq(&map_to_jobjects!(stmts)),
            self.jni.new_seq(&map_to_jobjects!(scoped_decls))
        )
    }

    pub fn comment(&self, comment: &str) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Seqn::with(self.env).new(
            self.jni.new_seq(&[]),
            self.jni.new_seq(&[]),
            self.no_position().to_jobject(),
            self.simple_info(&[comment]),
            self.no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn if_stmt(&self, cond: Expr, then_body: Stmt, else_body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::If,
            cond.to_jobject(),
            then_body.to_jobject(),
            else_body.to_jobject()
        )
    }

    pub fn while_stmt(&self, cond: Expr, invs: &[Expr], body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::While,
            cond.to_jobject(),
            self.jni.new_seq(&map_to_jobjects!(invs)),
            body.to_jobject()
        )
    }

    pub fn label(&self, name: &str, invs: &[Expr]) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Label,
            self.jni.new_string(name),
            self.jni.new_seq(&map_to_jobjects!(invs))
        )
    }

    pub fn goto(&self, target: &str) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Goto, self.jni.new_string(target))
    }

    pub fn fresh(&self, vars: &[Expr]) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Fresh,
            self.jni.new_seq(&map_to_jobjects!(vars))
        )
    }

    pub fn constraining(&self, vars: &[Expr], body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Constraining,
            self.jni.new_seq(&map_to_jobjects!(vars)),
            body.to_jobject()
        )
    }
}
