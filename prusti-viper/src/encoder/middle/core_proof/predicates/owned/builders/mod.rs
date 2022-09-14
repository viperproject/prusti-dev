mod common;
mod frac_ref;
mod owned_non_aliased;
mod owned_aliased;
mod unique_ref;

pub(super) use self::{
    common::predicate_decl::PredicateDeclBuilderMethods,
    frac_ref::{
        function_decl::FracRefSnapFunctionBuilder, function_use::FracRefSnapCallBuilder,
        predicate_decl::FracRefBuilder,
    },
    owned_aliased::{
        function_decl::OwnedAliasedSnapFunctionBuilder, predicate_decl::OwnedAliasedBuilder,
    },
    owned_non_aliased::{
        function_decl::OwnedNonAliasedSnapFunctionBuilder, predicate_decl::OwnedNonAliasedBuilder,
    },
    unique_ref::{
        function_decl::UniqueRefSnapFunctionBuilder, function_use::UniqueRefSnapCallBuilder,
        predicate_decl::UniqueRefBuilder,
    },
};
pub(in super::super::super) use self::{
    frac_ref::predicate_use::FracRefUseBuilder,
    owned_aliased::{
        function_use::OwnedAliasedSnapCallBuilder,
        predicate_range_use::OwnedAliasedRangeUseBuilder, predicate_use::OwnedAliasedUseBuilder,
    },
    owned_non_aliased::{
        function_use::OwnedNonAliasedSnapCallBuilder, predicate_use::OwnedNonAliasedUseBuilder,
    },
    unique_ref::predicate_use::UniqueRefUseBuilder,
};
