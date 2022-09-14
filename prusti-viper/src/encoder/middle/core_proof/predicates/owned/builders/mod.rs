mod common;
mod frac_ref;
mod owned_non_aliased;
mod owned_aliased;
mod unique_ref;

pub(super) use self::{
    common::predicate_decl::PredicateDeclBuilderMethods,
    frac_ref::{
        function_decl::FracRefSnapFunctionBuilder,
        function_range_decl::FracRefRangeSnapFunctionBuilder, function_use::FracRefSnapCallBuilder,
        predicate_decl::FracRefBuilder,
    },
    owned_aliased::function_range_decl::OwnedAliasedRangeSnapFunctionBuilder,
    owned_non_aliased::{
        function_decl::OwnedNonAliasedSnapFunctionBuilder, predicate_decl::OwnedNonAliasedBuilder,
    },
    unique_ref::{
        function_current_decl::UniqueRefCurrentSnapFunctionBuilder,
        function_current_range_decl::UniqueRefCurrentRangeSnapFunctionBuilder,
        function_current_use::UniqueRefCurrentSnapCallBuilder,
        function_final_decl::UniqueRefFinalSnapFunctionBuilder,
        function_final_range_decl::UniqueRefFinalRangeSnapFunctionBuilder,
        function_final_use::UniqueRefFinalSnapCallBuilder, predicate_decl::UniqueRefBuilder,
    },
};
pub(in super::super::super) use self::{
    frac_ref::{
        function_range_use::FracRefRangeSnapCallBuilder,
        predicate_range_use::FracRefRangeUseBuilder, predicate_use::FracRefUseBuilder,
    },
    owned_aliased::{
        function_range_use::OwnedAliasedRangeSnapCallBuilder,
        // function_use::OwnedAliasedSnapCallBuilder,
        predicate_range_use::OwnedAliasedRangeUseBuilder,
    },
    owned_non_aliased::{
        function_use::OwnedNonAliasedSnapCallBuilder, predicate_use::OwnedNonAliasedUseBuilder,
    },
    unique_ref::{
        function_current_range_use::UniqueRefCurrentRangeSnapCallBuilder,
        function_final_range_use::UniqueRefFinalRangeSnapCallBuilder,
        predicate_range_use::UniqueRefRangeUseBuilder, predicate_use::UniqueRefUseBuilder,
    },
};
