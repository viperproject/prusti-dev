use super::{
    encoder::PredicateEncoder, FracRefUseBuilder, OwnedNonAliasedUseBuilder, UniqueRefUseBuilder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{builtin_methods::CallContext, lowerer::Lowerer, types::TypesInterface},
};
use rustc_hash::FxHashSet;
use vir_crate::{
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    unfolded_owned_non_aliased_predicates: FxHashSet<vir_mid::Type>,
    used_unique_ref_predicates: FxHashSet<vir_mid::Type>,
}

pub(in super::super::super) trait PredicatesOwnedInterface {
    /// Marks that `OwnedNonAliased<ty>` was unfolded in the program and we need
    /// to provide its body.
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    /// Marks that `UniqueRef<ty>` was used in the program.
    fn mark_unique_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>>;
    /// A version of `owned_non_aliased` for the most common case.
    fn owned_non_aliased_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        final_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesOwnedInterface for Lowerer<'p, 'v, 'tcx> {
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .owned
            .unfolded_owned_non_aliased_predicates
            .contains(ty)
        {
            self.ensure_type_definition(ty)?;
            self.predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates
                .insert(ty.clone());
        }
        Ok(())
    }

    fn mark_unique_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .owned
            .used_unique_ref_predicates
            .contains(ty)
        {
            self.predicates_encoding_state
                .owned
                .used_unique_ref_predicates
                .insert(ty.clone());
        }
        Ok(())
    }

    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>> {
        let unfolded_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates,
        );
        let used_unique_ref_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .used_unique_ref_predicates,
        );
        let mut predicate_encoder = PredicateEncoder::new(self, &unfolded_predicates);
        for ty in &unfolded_predicates {
            predicate_encoder.encode_owned_non_aliased(ty)?;
        }
        for ty in &used_unique_ref_predicates {
            predicate_encoder.encode_unique_ref(ty)?;
        }
        Ok(predicate_encoder.into_predicates())
    }

    fn owned_non_aliased_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.owned_non_aliased(
            context,
            ty,
            generics,
            place.clone().into(),
            root_address.clone().into(),
            snapshot.clone().into(),
            None,
        )
    }

    fn owned_non_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = OwnedNonAliasedUseBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            snapshot,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        Ok(builder.build())
    }

    fn unique_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        final_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.unique_ref(
            context,
            ty,
            generics,
            place.clone().into(),
            root_address.clone().into(),
            current_snapshot.clone().into(),
            final_snapshot.clone().into(),
            lifetime.clone().into(),
        )
    }

    fn unique_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = UniqueRefUseBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            current_snapshot,
            final_snapshot,
            lifetime,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }

    fn frac_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.frac_ref(
            context,
            ty,
            generics,
            place.clone().into(),
            root_address.clone().into(),
            current_snapshot.clone().into(),
            lifetime.clone().into(),
        )
    }

    fn frac_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = FracRefUseBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            current_snapshot,
            lifetime,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }
}
