#![allow(dead_code)]

use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;

jobject_wrapper!(Expr);

impl<'a> AstFactory<'a> {
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
