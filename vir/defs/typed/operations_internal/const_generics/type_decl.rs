use super::{
    super::super::ast::{
        expression::Expression,
        type_decl::{self, TypeDecl},
    },
    WithConstArguments,
};

impl WithConstArguments for TypeDecl {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.get_const_parameters()
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect()
    }
}

impl WithConstArguments for type_decl::Struct {
    fn get_const_arguments(&self) -> Vec<Expression> {
        self.const_parameters
            .iter()
            .map(|parameter| parameter.clone().into())
            .collect()
    }
}
