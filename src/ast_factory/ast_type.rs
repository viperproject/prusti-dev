use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;
use ast_factory::structs::Type;

impl<'a> AstFactory<'a> {
    pub fn int_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Int_object)
    }

    pub fn bool_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Bool_object)
    }

    pub fn perm_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Perm_object)
    }

    pub fn ref_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Ref_object)
    }

    pub fn type_var(&self, name: &str) -> Type<'a> {
        let java_name = self.jni.new_string(name);
        let obj = self.jni.unwrap_result(
            ast::TypeVar::with(self.env).new(java_name),
        );
        Type::new(obj)
    }
}
