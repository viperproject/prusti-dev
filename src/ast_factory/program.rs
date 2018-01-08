#![allow(dead_code)]

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Expr;
use ast_factory::structs::Stmt;
use ast_factory::structs::Program;
use ast_factory::structs::Method;

impl<'a> AstFactory<'a> {
    pub fn new_program(&self, methods: Vec<Method>) -> Program<'a> {
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
        body: Option<Stmt>,
        pres: Vec<Expr>,
        posts: Vec<Expr>,
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
            match body {
                None => self.jni.new_option(None),
                Some(x) => self.jni.new_option(Some(x.to_jobject())),
            }
        )
    }
}
