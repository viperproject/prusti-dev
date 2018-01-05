#![allow(dead_code)]

use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;

jobject_wrapper!(Type);

impl<'a> AstFactory<'a> {
    pub fn new_int(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Int_object)
    }

    pub fn new_bool(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Bool_object)
    }

    pub fn new_perm(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Perm_object)
    }

    pub fn new_ref(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Ref_object)
    }
}
