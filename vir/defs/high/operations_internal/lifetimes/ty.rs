use super::{
    super::super::ast::ty::{self, LifetimeConst},
    common::get_lifetimes_with_arguments,
    WithLifetimes,
};

impl WithLifetimes for ty::Type {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        match self {
            ty::Type::Reference(reference) => reference.get_lifetimes(),
            ty::Type::Tuple(ty::Tuple {
                arguments,
                lifetimes,
                ..
            })
            | ty::Type::Union(ty::Union {
                arguments,
                lifetimes,
                ..
            })
            | ty::Type::Projection(ty::Projection {
                arguments,
                lifetimes,
                ..
            })
            | ty::Type::Enum(ty::Enum {
                arguments,
                lifetimes,
                ..
            })
            | ty::Type::Struct(ty::Struct {
                arguments,
                lifetimes,
                ..
            }) => get_lifetimes_with_arguments(lifetimes, arguments),
            ty::Type::Sequence(ty::Sequence { lifetimes, .. })
            | ty::Type::Map(ty::Map { lifetimes, .. })
            | ty::Type::Array(ty::Array { lifetimes, .. })
            | ty::Type::Slice(ty::Slice { lifetimes, .. })
            | ty::Type::Trusted(ty::Trusted { lifetimes, .. }) => lifetimes.clone(),
            _ => vec![],
        }
    }
}

impl WithLifetimes for ty::Reference {
    fn get_lifetimes(&self) -> Vec<LifetimeConst> {
        let mut lifetimes = vec![self.lifetime.clone()];
        let target_lifetimes = self.target_type.get_lifetimes();
        lifetimes.extend(target_lifetimes);
        lifetimes
    }
}
