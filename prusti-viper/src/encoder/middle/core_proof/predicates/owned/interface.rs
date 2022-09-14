use super::{
    builders::{
        FracRefSnapCallBuilder, OwnedAliasedRangeUseBuilder, OwnedAliasedUseBuilder,
        OwnedNonAliasedSnapCallBuilder, UniqueRefSnapCallBuilder,
    },
    encoder::PredicateEncoder,
    FracRefUseBuilder, OwnedAliasedSnapCallBuilder, OwnedNonAliasedUseBuilder, UniqueRefUseBuilder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, builtin_methods::CallContext, lowerer::Lowerer,
        places::PlacesInterface, types::TypesInterface,
    },
};
use prusti_common::config;
use rustc_hash::FxHashSet;
use vir_crate::{
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes, ty::Typed},
    },
};

#[derive(Default)]
pub(in super::super) struct PredicatesOwnedState {
    unfolded_owned_non_aliased_predicates: FxHashSet<vir_mid::Type>,
    unfolded_owned_aliased_predicates: FxHashSet<vir_mid::Type>,
    used_unique_ref_predicates: FxHashSet<vir_mid::Type>,
    snap_wrappers: FxHashSet<String>,
}

pub(in super::super::super) trait PredicatesOwnedInterface {
    /// Marks that `OwnedNonAliased<ty>` was unfolded in the program and we need
    /// to provide its body.
    fn mark_owned_non_aliased_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    /// Marks that `OwnedAliased<ty>` was unfolded in the program and we need to
    /// provide its body.
    fn mark_owned_aliased_as_unfolded(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    /// Marks that `UniqueRef<ty>` was used in the program.
    fn mark_unique_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_low::PredicateDecl>>;
    /// A version of `owned_non_aliased` for the most common case.
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
        must_be_predicate: bool,
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
    /// The result is guaranteed to be a `acc(predicate)`, which is needed
    /// for fold/unfold operations.
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased_predicate<G>(
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
    fn owned_non_aliased_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_aliased_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    // fn wrap_snap_into_bool(
    //     &mut self,
    //     ty: &vir_mid::Type,
    //     expression: vir_low::Expression,
    // ) -> SpannedEncodingResult<vir_low::Expression>;
    #[allow(clippy::too_many_arguments)]
    fn owned_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    fn owned_aliased_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
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
        target_slice_len: Option<vir_low::Expression>,
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
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        is_final: bool,
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
    fn frac_ref_full_vars_opt<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &Option<vir_low::VariableDecl>,
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
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_opt<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: Option<vir_low::Expression>,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    fn frac_ref_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    // /// A snap function that is chosen based on whether the place is behind
    // /// a reference or not.
    // fn place_snap<G>(
    //     &mut self,
    //     context: CallContext,
    //     ty: &vir_mid::Type,
    //     generics: &G,
    //     place: &vir_mid::Expression,
    //     position: vir_low::Position,
    //     deref_to_final: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression>
    // where
    //     G: WithLifetimes + WithConstArguments;
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

    fn mark_owned_aliased_as_unfolded(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .owned
            .unfolded_owned_aliased_predicates
            .contains(ty)
        {
            self.ensure_type_definition(ty)?;
            self.predicates_encoding_state
                .owned
                .unfolded_owned_aliased_predicates
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
        let unfolded_owned_non_aliased_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .unfolded_owned_non_aliased_predicates,
        );
        let unfolded_owned_aliased_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .unfolded_owned_aliased_predicates,
        );
        let used_unique_ref_predicates = std::mem::take(
            &mut self
                .predicates_encoding_state
                .owned
                .used_unique_ref_predicates,
        );
        let mut predicate_encoder = PredicateEncoder::new(self);
        for ty in &unfolded_owned_non_aliased_predicates {
            predicate_encoder.encode_owned_non_aliased(ty)?;
        }
        for ty in &unfolded_owned_aliased_predicates {
            predicate_encoder.encode_owned_aliased(ty)?;
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
        must_be_predicate: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        if must_be_predicate {
            self.owned_non_aliased_predicate(
                context,
                ty,
                generics,
                place.clone().into(),
                root_address.clone().into(),
                snapshot.clone().into(),
                None,
            )
        } else {
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
        let mut builder =
            OwnedNonAliasedUseBuilder::new(self, context, ty, generics, place, root_address)?;
        builder.add_snapshot_argument(snapshot)?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn owned_non_aliased_predicate<G>(
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
        let mut builder =
            OwnedNonAliasedUseBuilder::new(self, context, ty, generics, place, root_address)?;
        if config::use_snapshot_parameters_in_predicates() {
            builder.add_snapshot_argument(snapshot)?;
        }
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn owned_non_aliased_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = OwnedNonAliasedSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            position,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn owned_aliased_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder =
            OwnedAliasedSnapCallBuilder::new(self, context, ty, generics, address, position)?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    // fn wrap_snap_into_bool(
    //     &mut self,
    //     ty: &vir_mid::Type,
    //     expression: vir_low::Expression,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let ty_identifier = ty.get_identifier();
    //     let name = format!("snap_call_wrapper${}", ty_identifier);
    //     let domain_name = "SnapCallWrappers";
    //     let position = expression.position();
    //     if !self
    //         .predicates_encoding_state
    //         .owned
    //         .snap_wrappers
    //         .contains(&ty_identifier)
    //     {
    //         use vir_low::macros::*;
    //         var_decls!(
    //             snapshot: { ty.to_snapshot(self)? }
    //         );
    //         let call = self.create_domain_func_app(
    //             domain_name,
    //             name.clone(),
    //             vec![snapshot.clone().into()],
    //             vir_low::Type::Bool,
    //             position,
    //         )?;
    //         let body = vir_low::Expression::forall(
    //             vec![snapshot],
    //             vec![vir_low::Trigger::new(vec![call.clone()])],
    //             call,
    //         );
    //         // let body = expr! {
    //         //     forall( snapshot: { ty.to_snapshot(self)? } :: [ {[call.clone()]} ] [call] )
    //         // };
    //         let axiom = vir_low::DomainAxiomDecl {
    //             name: format!("snap_call_wrapper_always_true${}", ty_identifier),
    //             body,
    //         };
    //         self.declare_axiom(domain_name, axiom)?;
    //         self.predicates_encoding_state
    //             .owned
    //             .snap_wrappers
    //             .insert(ty_identifier);
    //     }
    //     self.create_domain_func_app(
    //         domain_name,
    //         name,
    //         vec![expression],
    //         vir_low::Type::Bool,
    //         position,
    //     )
    // }

    fn owned_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_owned_aliased_as_unfolded(ty)?;
        let mut builder = OwnedAliasedUseBuilder::new(self, context, ty, generics, address)?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn owned_aliased_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let builder = OwnedAliasedRangeUseBuilder::new(
            self,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            permission_amount,
        )?;
        builder.build()
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
        target_slice_len: Option<vir_low::Expression>,
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
            target_slice_len,
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
        target_slice_len: Option<vir_low::Expression>,
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
            // current_snapshot,
            // final_snapshot,
            lifetime,
            target_slice_len,
        )?;
        builder.add_current_snapshot_argument(current_snapshot)?;
        // builder.add_snapshot_arguments(current_snapshot, final_snapshot)?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn unique_ref_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
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
            // final_snapshot,
            lifetime,
            target_slice_len,
        )?;
        // if config::use_snapshot_parameters_in_predicates() {
        //     builder.add_snapshot_arguments(current_snapshot, final_snapshot)?;
        // }
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn unique_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        is_final: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = UniqueRefSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            lifetime,
            target_slice_len,
            is_final,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
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

    fn frac_ref_full_vars_opt<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        root_address: &vir_low::VariableDecl,
        current_snapshot: &Option<vir_low::VariableDecl>,
        lifetime: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = FracRefUseBuilder::new(
            self,
            context,
            ty,
            generics,
            place.clone().into(),
            root_address.clone().into(),
            lifetime.clone().into(),
        )?;
        if let Some(current_snapshot) = current_snapshot {
            builder.add_snapshot_argument(current_snapshot.clone().into())?;
        }
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
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
        self.frac_ref_opt(
            context,
            ty,
            generics,
            place,
            root_address,
            Some(current_snapshot),
            lifetime,
        )
    }

    fn frac_ref_opt<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: Option<vir_low::Expression>,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder =
            FracRefUseBuilder::new(self, context, ty, generics, place, root_address, lifetime)?;
        if let Some(current_snapshot) = current_snapshot {
            builder.add_snapshot_argument(current_snapshot)?;
        }
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn frac_ref_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        // FIXME: Remove the current_snapshto argument.
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
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
            lifetime,
            // target_slice_len,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn frac_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = FracRefSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            root_address,
            lifetime,
            target_slice_len,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    // fn place_snap<G>(
    //     &mut self,
    //     context: CallContext,
    //     ty: &vir_mid::Type,
    //     generics: &G,
    //     place: &vir_mid::Expression,
    //     position: vir_low::Position,
    //     deref_to_final: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression>
    // where
    //     G: WithLifetimes + WithConstArguments,
    // {
    //     let place_low = self.encode_expression_as_place(place)?;
    //     let root_address = self.extract_root_address(place)?;
    //     if let Some(reference_place) = place.get_first_dereferenced_reference() {
    //         let vir_mid::Type::Reference(reference_type) = reference_place.get_type() else {
    //             unreachable!()
    //         };
    //         let TODO_target_slice_len = None;
    //         match reference_type.uniqueness {
    //             vir_mid::ty::Uniqueness::Unique => {
    //                 self.unique_ref_snap(
    //                     context, ty, generics, place_low, root_address,
    //                     reference_type.lifetime, TODO_target_slice_len, deref_to_final)
    //             },
    //             vir_mid::ty::Uniqueness::Shared => todo!(),
    //         }
    //     } else {
    //         self.owned_non_aliased_snap(
    //             context,
    //             ty,
    //             generics,
    //             place_low,
    //             root_address,
    //             position,
    //         )
    //     }
    // }
}
