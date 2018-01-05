#![allow(dead_code)]

use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::expression::Expr;
use ast_factory::statement::Stmt;

jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Field);
jobject_wrapper!(LocalVarDecl);

impl<'a> AstFactory<'a> {
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
}
