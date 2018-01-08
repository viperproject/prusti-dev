#![allow(dead_code)]

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Expr;
use ast_factory::structs::Field;
use ast_factory::structs::Position;
use ast_factory::structs::LocalVarDecl;
use ast_factory::structs::Stmt;

impl<'a> AstFactory<'a> {
    pub fn new_new_stmt(&self, lhs: Expr, fields: Vec<Field>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::NewStmt,
            lhs.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(fields))
        )
    }

    pub fn new_local_var_assign(&self, lhs: Expr, rhs: Expr) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::LocalVarAssign,
            lhs.to_jobject(),
            rhs.to_jobject()
        )
    }

    pub fn new_field_assign(&self, lhs: Expr, rhs: Expr) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::FieldAssign,
            lhs.to_jobject(),
            rhs.to_jobject()
        )
    }

    pub fn new_method_call(
        &self,
        method_name: &str,
        args: Vec<Expr>,
        targets: Vec<Expr>,
    ) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::MethodCall,
            self.jni.new_string(method_name),
            self.jni.new_seq(map_to_jobjects!(args)),
            self.jni.new_seq(map_to_jobjects!(targets))
        )
    }

    pub fn new_exhale(&self, expr: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Exhale, expr.to_jobject())
    }

    pub fn new_inhale(&self, expr: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Inhale, expr.to_jobject())
    }

    pub fn new_assert(&self, expr: Expr, pos: Position) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn new_assert_with_comment(&self, expr: Expr, pos: Position, comment: &str) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.new_simple_info(
                vec![comment],
            ),
            self.new_no_trafos(),
        ));
        Stmt::new(obj)
    }

    pub fn new_fold(&self, acc: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Fold, acc.to_jobject())
    }

    pub fn new_unfold(&self, acc: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Unfold, acc.to_jobject())
    }

    pub fn new_package(&self, wand: Expr, proof_script: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Package,
            wand.to_jobject(),
            proof_script.to_jobject()
        )
    }

    pub fn new_apply(&self, wand: Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Apply, wand.to_jobject())
    }

    pub fn new_seqn(&self, stmts: Vec<Stmt>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Seqn,
            self.jni.new_seq(map_to_jobjects!(stmts)),
            self.jni.new_seq(vec![])
        )
    }

    pub fn new_if(&self, cond: Expr, then_body: Stmt, else_body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::If,
            cond.to_jobject(),
            then_body.to_jobject(),
            else_body.to_jobject()
        )
    }

    pub fn new_while(&self, cond: Expr, invs: Vec<Expr>, body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::While,
            cond.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(invs)),
            body.to_jobject()
        )
    }

    pub fn new_label(&self, name: &str, invs: Vec<Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Label,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(invs))
        )
    }

    pub fn new_goto(&self, target: &str) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Goto, self.jni.new_string(target))
    }

    pub fn new_fresh(&self, vars: Vec<Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Fresh,
            self.jni.new_seq(map_to_jobjects!(vars))
        )
    }

    pub fn new_constraining(&self, vars: Vec<Expr>, body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Constraining,
            self.jni.new_seq(map_to_jobjects!(vars)),
            body.to_jobject()
        )
    }

    pub fn new_local_var_decl_stmt(&self, decl: LocalVarDecl) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::LocalVarDeclStmt, decl.to_jobject())
    }
}
