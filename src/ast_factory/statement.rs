use viper_sys::wrappers::viper::silver::ast;
use jni::objects::JObject;
use ast_factory::AstFactory;
use ast_factory::structs::Expr;
use ast_factory::structs::Field;
use ast_factory::structs::Position;
use ast_factory::structs::LocalVarDecl;
use ast_factory::structs::Stmt;

impl<'a> AstFactory<'a> {
    pub fn new_stmt(&self, lhs: Expr, fields: Vec<Field>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::NewStmt,
            lhs.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(fields))
        )
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

    pub fn method_call(&self, method_name: &str, args: Vec<Expr>, targets: Vec<Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::MethodCall,
            self.jni.new_string(method_name),
            self.jni.new_seq(map_to_jobjects!(args)),
            self.jni.new_seq(map_to_jobjects!(targets))
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
            self.simple_info(vec![comment]),
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
            self.simple_info(vec![comment]),
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
            self.simple_info(vec![comment]),
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

    /// Here the argument `scoped_decls` is a vector of `LocalVarDecl`, but Viper allows also
    /// labels, methods, domains and so on.
    pub fn seqn(&self, stmts: Vec<Stmt>, scoped_decls: Vec<LocalVarDecl>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Seqn,
            self.jni.new_seq(map_to_jobjects!(stmts)),
            self.jni.new_seq(map_to_jobjects!(scoped_decls))
        )
    }

    // TODO: merge somehow with `self.seqn`
    pub fn seqn_with_labels(
        &self,
        stmts: Vec<Stmt>,
        scoped_decls: Vec<LocalVarDecl>,
        scoped_labels: Vec<Stmt>,
    ) -> Stmt<'a> {
        let decls: Vec<JObject> = map_to_jobjects!(scoped_decls);
        let labels: Vec<JObject> = map_to_jobjects!(scoped_labels);
        build_ast_node!(
            self,
            Stmt,
            ast::Seqn,
            self.jni.new_seq(map_to_jobjects!(stmts)),
            self.jni.new_seq(vec![decls, labels].concat())
        )
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

    pub fn while_stmt(&self, cond: Expr, invs: Vec<Expr>, body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::While,
            cond.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(invs)),
            body.to_jobject()
        )
    }

    pub fn label(&self, name: &str, invs: Vec<Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Label,
            self.jni.new_string(name),
            self.jni.new_seq(map_to_jobjects!(invs))
        )
    }

    pub fn goto(&self, target: &str) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Goto, self.jni.new_string(target))
    }

    pub fn fresh(&self, vars: Vec<Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Fresh,
            self.jni.new_seq(map_to_jobjects!(vars))
        )
    }

    pub fn constraining(&self, vars: Vec<Expr>, body: Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Constraining,
            self.jni.new_seq(map_to_jobjects!(vars)),
            body.to_jobject()
        )
    }
}
