#![allow(dead_code)]

use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Type;

impl<'a> AstFactory<'a> {
    pub fn new_int_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Int_object)
    }

    pub fn new_bool_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Bool_object)
    }

    pub fn new_perm_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Perm_object)
    }

    pub fn new_ref_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Ref_object)
    }

    pub fn new_type_var(&self, name: &str) -> Type<'a> {
        let java_name = self.jni.new_string(name);
        let obj = self.jni.unwrap_result(
            ast::TypeVar::with(self.env).new(java_name),
        );
        Type::new(obj)
    }
}
