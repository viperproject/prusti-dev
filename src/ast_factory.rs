#![allow(dead_code)]

use jni::JNIEnv;
use jni::sys::jint;
use jni::objects::JObject;
use jni_utils::JniUtils;
#[allow(unused_imports)]
use viper_sys::wrappers::*;
#[allow(unused_imports)]
use viper_sys::wrappers::viper::silver::ast;

pub struct AstFactory<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
}

macro_rules! jobject_wrapper {
    ($name:ident) => (
        pub struct $name<'a> { obj: JObject<'a> }
        impl<'a> $name<'a> {
            fn new(obj: JObject<'a>) -> Self {
                $name { obj }
            }
            pub fn to_jobject(&self) -> JObject {
                self.obj
            }
        }
    );
}

macro_rules! map_to_jobject {
    ($item:expr) => (
        $item.map(|x| x.to_jobject())
    );
}

macro_rules! map_to_jobjects {
    ($items:expr) => (
        map_to_jobject!($items.iter()).collect()
    );
}

jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Field);
jobject_wrapper!(LocalVarDecl);
jobject_wrapper!(Stmt);
jobject_wrapper!(Expr);
jobject_wrapper!(Position);

macro_rules! build_ast_node {
    ($self:expr, $wrapper:path, $($java_class:ident)::+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper { obj }
        }
    };
    ($self:expr, $wrapper:path, $($java_class:ident)::+, $($args:expr),+) => {
         {
            let obj = $self.jni.unwrap_result($($java_class)::+::with($self.env).new(
                $($args),+ ,
                $self.new_no_position().to_jobject(),
                $self.new_no_info(),
                $self.new_no_trafos(),
            ));
            $wrapper { obj }
        }
    };
}

impl<'a> AstFactory<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        AstFactory { env, jni }
    }

    pub fn new_no_position(&self) -> Position {
        let obj = self.jni.unwrap_result(
            ast::NoPosition_object::with(self.env).singleton(),
        );
        Position { obj }
    }

    pub fn new_line_column_position(&self, line: jint, column: jint) -> Position {
        let obj = self.jni.unwrap_result(
            ast::LineColumnPosition::with(self.env).new(
                line,
                column,
            ),
        );
        Position { obj }
    }

    pub fn new_identifier_position(&self, line: jint, column: jint, pos_id: &str) -> Position {
        let obj = self.jni.unwrap_result(
            ast::IdentifierPosition::with(self.env).new(
                self.jni.unwrap_result(
                    java::nio::file::Paths::with(self.env).call_get(
                        self.jni.new_string(""),
                        self.jni.new_object_array(0),
                    ),
                ),
                self.new_line_column_position(line, column).to_jobject(),
                self.jni.new_option(None),
                self.jni.new_string(pos_id),
            ),
        );
        Position { obj }
    }

    fn new_no_info(&self) -> JObject {
        self.jni.unwrap_result(
            ast::NoInfo_object::with(self.env).singleton(),
        )
    }

    fn new_simple_info(&self, comments: Vec<String>) -> JObject {
        self.jni.unwrap_result(ast::SimpleInfo::with(self.env).new(
            self.jni.new_seq(
                comments.iter().map(|x| self.jni.new_string(x)).collect(),
            ),
        ))
    }

    fn new_no_trafos(&self) -> JObject {
        self.jni.unwrap_result(
            ast::NoTrafos_object::with(self.env).singleton(),
        )
    }

    pub fn new_program(&self, methods: Vec<&Method>) -> Program<'a> {
        build_ast_node!(
            self,
            Program,
            ast::Program,
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(map_to_jobjects!(methods))
        )
    }

    pub fn new_method(
        &self,
        name: &str,
        body: Option<&Stmt>,
        pres: Vec<&Expr>,
        posts: Vec<&Expr>,
    ) -> Method<'a> {
        build_ast_node!(
            self,
            Method,
            ast::Method,
            self.jni.new_string(name),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(map_to_jobjects!(pres)),
            self.jni.new_seq(map_to_jobjects!(posts)),
            self.jni.new_option(body.map(|x| x.to_jobject()))
        )
    }

    // === Statements ===

    pub fn new_new_stmt(&self, lhs: &Expr, fields: Vec<&Field>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::NewStmt,
            lhs.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(fields))
        )
    }

    pub fn new_local_var_assign(&self, lhs: &Expr, rhs: &Expr) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::LocalVarAssign,
            lhs.to_jobject(),
            rhs.to_jobject()
        )
    }

    pub fn new_field_assign(&self, lhs: &Expr, rhs: &Expr) -> Stmt<'a> {
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
        args: Vec<&Expr>,
        targets: Vec<&Expr>,
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

    pub fn new_exhale(&self, expr: &Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Exhale, expr.to_jobject())
    }

    pub fn new_inhale(&self, expr: &Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Inhale, expr.to_jobject())
    }

    pub fn new_assert(&self, expr: &Expr, pos: Position) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Stmt { obj }
    }

    pub fn new_assert_with_comment(&self, expr: &Expr, pos: Position, comment: String) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            pos.to_jobject(),
            self.new_simple_info(
                vec![comment],
            ),
            self.new_no_trafos(),
        ));
        Stmt { obj }
    }

    pub fn new_fold(&self, acc: &Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Fold, acc.to_jobject())
    }

    pub fn new_unfold(&self, acc: &Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Unfold, acc.to_jobject())
    }

    pub fn new_package(&self, wand: &Expr, proof_script: &Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Package,
            wand.to_jobject(),
            proof_script.to_jobject()
        )
    }

    pub fn new_apply(&self, wand: &Expr) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::Apply, wand.to_jobject())
    }

    pub fn new_seqn(&self, stmts: Vec<&Stmt>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Seqn,
            self.jni.new_seq(map_to_jobjects!(stmts)),
            self.jni.new_seq(vec![])
        )
    }

    pub fn new_if(&self, cond: &Expr, then_body: &Stmt, else_body: &Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::If,
            cond.to_jobject(),
            then_body.to_jobject(),
            else_body.to_jobject()
        )
    }

    pub fn new_while(&self, cond: &Expr, invs: Vec<&Expr>, body: &Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::While,
            cond.to_jobject(),
            self.jni.new_seq(map_to_jobjects!(invs)),
            body.to_jobject()
        )
    }

    pub fn new_label(&self, name: &str, invs: Vec<&Expr>) -> Stmt<'a> {
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

    pub fn new_fresh(&self, vars: Vec<&Expr>) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Fresh,
            self.jni.new_seq(map_to_jobjects!(vars))
        )
    }

    pub fn new_constraining(&self, vars: Vec<&Expr>, body: &Stmt) -> Stmt<'a> {
        build_ast_node!(
            self,
            Stmt,
            ast::Constraining,
            self.jni.new_seq(map_to_jobjects!(vars)),
            body.to_jobject()
        )
    }

    pub fn new_local_var_decl_stmt(&self, decl: &LocalVarDecl) -> Stmt<'a> {
        build_ast_node!(self, Stmt, ast::LocalVarDeclStmt, decl.to_jobject())
    }

    // === Boolean expressions ===

    pub fn new_or(&self, left: &Expr, right: &Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Or, left.to_jobject(), right.to_jobject())
    }

    pub fn new_and(&self, left: &Expr, right: &Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::And, left.to_jobject(), right.to_jobject())
    }

    pub fn new_implies(&self, left: &Expr, right: &Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::Implies,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_magic_wand(&self, left: &Expr, right: &Expr) -> Expr<'a> {
        build_ast_node!(
            self,
            Expr,
            ast::MagicWand,
            left.to_jobject(),
            right.to_jobject()
        )
    }

    pub fn new_not(&self, expr: &Expr) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::Not, expr.to_jobject())
    }

    pub fn new_true_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::TrueLit)
    }

    pub fn new_false_lit(&self) -> Expr<'a> {
        build_ast_node!(self, Expr, ast::FalseLit)
    }
}
