use super::{
    super::super::ast::{
        ty::LifetimeConst,
        type_decl::{self, TypeDecl},
    },
    WithLifetimes,
};

impl WithLifetimes for TypeDecl {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.get_lifetime_parameters().to_owned()
    }
}

impl WithLifetimes for type_decl::Struct {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        self.lifetimes.clone()
    }
}
