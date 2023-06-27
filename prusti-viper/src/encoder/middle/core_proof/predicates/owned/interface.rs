use super::{
    builders::{
        FracRefRangeSnapCallBuilder, FracRefRangeUseBuilder, FracRefSnapCallBuilder,
        OwnedAliasedRangeSnapCallBuilder, OwnedAliasedRangeUseBuilder,
        OwnedNonAliasedSnapCallBuilder, UniqueRefCurrentRangeSnapCallBuilder,
        UniqueRefCurrentSnapCallBuilder, UniqueRefFinalRangeSnapCallBuilder,
        UniqueRefFinalSnapCallBuilder, UniqueRefRangeUseBuilder,
    },
    FracRefUseBuilder, OwnedNonAliasedUseBuilder, UniqueRefUseBuilder,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, lowerer::Lowerer, places::PlacesInterface,
        types::TypesInterface,
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low, operations::ty::Typed},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

// #[derive(Default)]
// pub(in super::super) struct PredicatesOwnedState {
//     unfolded_owned_predicates: FxHashSet<vir_mid::Type>,
//     used_unique_ref_predicates: FxHashSet<vir_mid::Type>,
//     used_frac_ref_predicates: FxHashSet<vir_mid::Type>,
//     used_owned_range_snapshot_functions: FxHashSet<vir_mid::Type>,
//     used_unique_ref_range_snapshot_functions: FxHashSet<vir_mid::Type>,
//     used_frac_ref_range_snapshot_functions: FxHashSet<vir_mid::Type>,
// }

/// Addidional information about the predicate used by purification
/// optimizations.
#[derive(Clone, Debug)]
pub(in super::super::super) struct OwnedPredicateInfo {
    /// Snapshot function of the current state.
    pub(in super::super::super) current_snapshot_function: SnapshotFunctionInfo,
    /// Snapshot function of the final state.
    pub(in super::super::super) final_snapshot_function: Option<SnapshotFunctionInfo>,
    /// The snapshot type.
    pub(in super::super::super) snapshot_type: vir_low::Type,
}

/// Addidional information about the snapshot function used by purification
/// optimizations.
#[derive(Clone, Debug)]
pub(in super::super::super) struct SnapshotFunctionInfo {
    /// The name of the snapshot function.
    pub(in super::super::super) function_name: String,
    /// The properties that we know to hold when we have a predicate instance.
    pub(in super::super::super) postconditions: Vec<vir_low::Expression>,
    /// The assertions that link the snapshot of the predicate with the
    /// snapshots of inner predicates.
    pub(in super::super::super) body: Vec<vir_low::Expression>,
}

pub(in super::super::super) trait PredicatesOwnedInterface {
    /// Marks that `Owned<ty>` was unfolded in the program and we need to
    /// provide its body.
    fn mark_owned_predicate_as_unfolded(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;
    /// Marks that `UniqueRef<ty>` was used in the program.
    fn mark_unique_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn mark_frac_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    // FIXME: Make this method to be defined on the state and take `self`.
    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<(
        Vec<vir_low::PredicateDecl>,
        BTreeMap<String, OwnedPredicateInfo>,
    )>;
    /// Owned predicate that can be either aliased or non-aliased depending on
    /// the value of `place`.
    fn owned_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    /// A version of `owned_non_aliased` for the most common case.
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased_full_vars_with_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
        position: vir_low::Position,
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
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_non_aliased_with_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        snapshot: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
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
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn owned_predicate_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
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
        address: vir_low::Expression,
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
    fn owned_aliased_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
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
        address: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_full_vars_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
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
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    fn unique_ref_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
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
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        is_final: bool,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn unique_ref_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        is_final: bool,
        position: vir_low::Position,
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
        address: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_full_vars_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
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
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    fn frac_ref_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
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
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
    #[allow(clippy::too_many_arguments)]
    fn frac_ref_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesOwnedInterface for Lowerer<'p, 'v, 'tcx> {
    fn mark_owned_predicate_as_unfolded(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        self.ensure_type_definition(ty)?;
        self.encode_owned_predicate(ty)?;
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .unfolded_owned_predicates
        //     .contains(ty)
        // {
        //     self.ensure_type_definition(ty)?;
        //     self.predicates_encoding_state
        //         .owned
        //         .unfolded_owned_predicates
        //         .insert(ty.clone());
        // }
        Ok(())
    }

    fn mark_unique_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        self.encode_unique_ref_predicate(ty)?;
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .used_unique_ref_predicates
        //     .contains(ty)
        // {
        //     self.predicates_encoding_state
        //         .owned
        //         .used_unique_ref_predicates
        //         .insert(ty.clone());
        // }
        Ok(())
    }

    fn mark_frac_ref_as_used(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        self.encode_frac_ref_predicate(ty)?;
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .used_frac_ref_predicates
        //     .contains(ty)
        // {
        //     self.predicates_encoding_state
        //         .owned
        //         .used_frac_ref_predicates
        //         .insert(ty.clone());
        // }
        Ok(())
    }

    fn collect_owned_predicate_decls(
        &mut self,
    ) -> SpannedEncodingResult<(
        Vec<vir_low::PredicateDecl>,
        BTreeMap<String, OwnedPredicateInfo>,
    )> {
        // // let unfolded_owned_predicates = std::mem::take(
        // //     &mut self
        // //         .predicates_encoding_state
        // //         .owned
        // //         .unfolded_owned_predicates,
        // // );
        // let unfolded_owned_predicates = std::mem::take(
        //     &mut self
        //         .predicates_encoding_state
        //         .owned
        //         .unfolded_owned_predicates,
        // );
        // let used_unique_ref_predicates = std::mem::take(
        //     &mut self
        //         .predicates_encoding_state
        //         .owned
        //         .used_unique_ref_predicates,
        // );
        // let used_owned_range_snapshot_functions = std::mem::take(
        //     &mut self
        //         .predicates_encoding_state
        //         .owned
        //         .used_owned_range_snapshot_functions,
        // );
        // let used_unique_ref_range_snapshot_functions = std::mem::take(
        //     &mut self
        //         .predicates_encoding_state
        //         .owned
        //         .used_unique_ref_range_snapshot_functions,
        // );
        // let used_frac_ref_range_snapshot_functions = std::mem::take(
        //     &mut self
        //         .predicates_encoding_state
        //         .owned
        //         .used_frac_ref_range_snapshot_functions,
        // );
        // let mut predicate_encoder = PredicateEncoder::new(self);
        // for ty in &unfolded_owned_predicates {
        //     predicate_encoder.encode_owned_non_aliased(ty)?;
        // }
        // // for ty in &unfolded_owned_predicates {
        // //     unimplemented!();
        // //     // predicate_encoder.encode_owned_aliased(ty)?;
        // // }
        // for ty in &used_unique_ref_predicates {
        //     predicate_encoder.encode_unique_ref(ty)?;
        // }
        // for ty in &used_owned_range_snapshot_functions {
        //     predicate_encoder.encode_owned_range_snapshot(ty)?;
        // }
        // for ty in &used_unique_ref_range_snapshot_functions {
        //     predicate_encoder.encode_unique_ref_range_snapshot(ty)?;
        // }
        // for ty in &used_frac_ref_range_snapshot_functions {
        //     predicate_encoder.encode_frac_ref_range_snapshot(ty)?;
        // }
        // let predicate_info = predicate_encoder.take_predicate_info();
        // Ok((predicate_encoder.into_predicates(), predicate_info))
        let predicates = std::mem::take(&mut self.predicates_encoding_state.owned.predicates);
        let predicate_info =
            std::mem::take(&mut self.predicates_encoding_state.owned.predicate_info);
        Ok((predicates, predicate_info))
    }

    fn owned_predicate<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_owned_predicate_as_unfolded(ty)?;
        let mut builder =
            OwnedNonAliasedUseBuilder::new(self, context, ty, generics, place, address, position)?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn owned_non_aliased_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.owned_non_aliased(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            None,
            position,
        )
    }

    fn owned_non_aliased_full_vars_with_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        snapshot: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.owned_non_aliased_with_snapshot(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            snapshot.clone().into(),
            None,
            position,
        )
    }

    fn owned_non_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.owned_predicate(
            context,
            ty,
            generics,
            place,
            address,
            permission_amount,
            position,
        )
    }

    fn owned_non_aliased_with_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        snapshot: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let predicate = self.owned_non_aliased(
            context,
            ty,
            generics,
            place.clone(),
            address.clone(),
            permission_amount,
            position,
        )?;
        let snap_call =
            self.owned_non_aliased_snap(context, ty, generics, place, address, position)?;
        Ok(vir_low::Expression::and(
            predicate,
            vir_low::Expression::equals(snapshot, snap_call),
        ))
    }

    fn owned_aliased<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let place = self.place_option_none_constructor(position)?;
        self.owned_non_aliased(
            context,
            ty,
            generics,
            place,
            address,
            permission_amount,
            position,
        )
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
        position: vir_low::Position,
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
            position,
        )?;
        builder.build()
    }

    fn owned_predicate_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_owned_predicate_as_unfolded(ty)?;
        let mut builder = OwnedNonAliasedSnapCallBuilder::new(
            self, context, ty, generics, place, address, position,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn owned_non_aliased_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.owned_predicate_snap(context, ty, generics, place, address, position)
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
        let place = self.place_option_none_constructor(position)?;
        self.owned_predicate_snap(context, ty, generics, place, address, position)
    }

    fn owned_aliased_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.ensure_type_definition(ty)?;
        self.encode_owned_predicate_range_snapshot(ty)?;
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .used_owned_range_snapshot_functions
        //     .contains(ty)
        // {
        //     self.ensure_type_definition(ty)?;
        //     self.predicates_encoding_state
        //         .owned
        //         .used_owned_range_snapshot_functions
        //         .insert(ty.clone());
        // }
        let builder = OwnedAliasedRangeSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            position,
        )?;
        builder.build()
    }

    fn unique_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.unique_ref(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            lifetime.clone().into(),
            target_slice_len,
            None,
            position,
        )
    }

    fn unique_ref_full_vars_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.unique_ref_with_current_snapshot(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            current_snapshot.clone().into(),
            lifetime.clone().into(),
            target_slice_len,
            None,
            position,
        )
    }

    fn unique_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_unique_ref_as_used(ty)?;
        let mut builder = UniqueRefUseBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            address,
            lifetime,
            target_slice_len,
            position,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn unique_ref_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let builder = UniqueRefRangeUseBuilder::new(
            self,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            lifetime,
            permission_amount,
            position,
        )?;
        builder.build()
    }

    fn unique_ref_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let predicate = self.unique_ref(
            context,
            ty,
            generics,
            place.clone(),
            address.clone(),
            lifetime.clone(),
            target_slice_len.clone(),
            permission_amount,
            position,
        )?;
        let snap_call = self.unique_ref_snap(
            context,
            ty,
            generics,
            place,
            address,
            lifetime,
            target_slice_len,
            false,
            position,
        )?;
        debug_assert_eq!(current_snapshot.get_type(), snap_call.get_type());
        Ok(vir_low::Expression::and(
            predicate,
            vir_low::Expression::equals(current_snapshot, snap_call),
        ))
    }

    fn unique_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        is_final: bool,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_unique_ref_as_used(ty)?;
        if is_final {
            let mut builder = UniqueRefFinalSnapCallBuilder::new(
                self,
                context,
                ty,
                generics,
                place,
                address,
                lifetime,
                target_slice_len,
                position,
            )?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        } else {
            let mut builder = UniqueRefCurrentSnapCallBuilder::new(
                self,
                context,
                ty,
                generics,
                place,
                address,
                lifetime,
                target_slice_len,
                position,
            )?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        }
    }

    fn unique_ref_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        is_final: bool,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.ensure_type_definition(ty)?;
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .used_unique_ref_range_snapshot_functions
        //     .contains(ty)
        // {
        //     self.ensure_type_definition(ty)?;
        //     self.predicates_encoding_state
        //         .owned
        //         .used_unique_ref_range_snapshot_functions
        //         .insert(ty.clone());
        // }
        if is_final {
            self.encode_unique_ref_predicate_final_range_snapshot(ty)?;
            let mut builder = UniqueRefFinalRangeSnapCallBuilder::new(
                self,
                context,
                ty,
                generics,
                address,
                start_index,
                end_index,
                lifetime,
                position,
            )?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        } else {
            self.encode_unique_ref_predicate_current_range_snapshot(ty)?;
            let mut builder = UniqueRefCurrentRangeSnapCallBuilder::new(
                self,
                context,
                ty,
                generics,
                address,
                start_index,
                end_index,
                lifetime,
                position,
            )?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        }
    }

    fn frac_ref_full_vars<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.frac_ref(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            lifetime.clone().into(),
            target_slice_len,
            None,
            position,
        )
    }

    fn frac_ref_full_vars_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: &vir_low::VariableDecl,
        address: &vir_low::VariableDecl,
        current_snapshot: &vir_low::VariableDecl,
        lifetime: &vir_low::VariableDecl,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.frac_ref_with_current_snapshot(
            context,
            ty,
            generics,
            place.clone().into(),
            address.clone().into(),
            current_snapshot.clone().into(),
            lifetime.clone().into(),
            target_slice_len,
            None,
            position,
        )
    }

    fn frac_ref<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
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
            address,
            lifetime,
            target_slice_len,
            position,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_permission_amount(permission_amount)?;
        builder.build()
    }

    fn frac_ref_range<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let builder = FracRefRangeUseBuilder::new(
            self,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            lifetime,
            permission_amount,
            position,
        )?;
        builder.build()
    }

    fn frac_ref_with_current_snapshot<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let predicate = self.frac_ref(
            context,
            ty,
            generics,
            place.clone(),
            address.clone(),
            lifetime.clone(),
            target_slice_len.clone(),
            permission_amount,
            position,
        )?;
        let snap_call = self.frac_ref_snap(
            context,
            ty,
            generics,
            place,
            address,
            lifetime,
            target_slice_len,
            position,
        )?;
        Ok(vir_low::Expression::and(
            predicate,
            vir_low::Expression::equals(current_snapshot, snap_call),
        ))
    }

    fn frac_ref_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        self.mark_frac_ref_as_used(ty)?;
        let mut builder = FracRefSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            place,
            address,
            lifetime,
            target_slice_len,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }

    fn frac_ref_range_snap<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        lifetime: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        G: WithLifetimes + WithConstArguments,
    {
        // if !self
        //     .predicates_encoding_state
        //     .owned
        //     .used_frac_ref_range_snapshot_functions
        //     .contains(ty)
        // {
        //     self.ensure_type_definition(ty)?;
        //     self.predicates_encoding_state
        //         .owned
        //         .used_frac_ref_range_snapshot_functions
        //         .insert(ty.clone());
        // }
        self.ensure_type_definition(ty)?;
        self.encode_frac_ref_predicate_range_snapshot(ty)?;
        let mut builder = FracRefRangeSnapCallBuilder::new(
            self,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            lifetime,
            position,
        )?;
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.build()
    }
}
