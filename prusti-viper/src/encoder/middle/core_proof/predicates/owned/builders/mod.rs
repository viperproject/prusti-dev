mod common;
mod frac_ref;
mod owned_non_aliased;
mod unique_ref;

pub(super) use self::{
    common::predicate_decl::PredicateDeclBuilderMethods, frac_ref::predicate_decl::FracRefBuilder,
    owned_non_aliased::predicate_decl::OwnedNonAliasedBuilder,
    unique_ref::predicate_decl::UniqueRefBuilder,
};
pub(in super::super::super) use self::{
    frac_ref::predicate_use::FracRefUseBuilder,
    owned_non_aliased::predicate_use::OwnedNonAliasedUseBuilder,
    unique_ref::predicate_use::UniqueRefUseBuilder,
};
