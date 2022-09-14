use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::builders::calls::BuiltinMethodCallBuilder, lowerer::Lowerer,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

#[derive(Clone, Copy)]
pub(in super::super::super) enum CallContext {
    BuiltinMethod,
    Procedure,
}

pub(in super::super::super) trait BuiltinMethodCallsInterface {
    #[allow(clippy::too_many_arguments)]
    fn call_write_place_constant_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_root_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;

    #[allow(clippy::too_many_arguments)]
    fn call_move_place_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_root_address: vir_low::Expression,
        source_place: vir_low::Expression,
        source_root_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;

    #[allow(clippy::too_many_arguments)]
    fn call_copy_place_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_root_address: vir_low::Expression,
        source_place: vir_low::Expression,
        source_root_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
        source_permission_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;

    #[allow(clippy::too_many_arguments)]
    fn call_into_memory_block_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        guard: Option<vir_low::Expression>,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;

    #[allow(clippy::too_many_arguments)]
    fn call_bor_shorten<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: Option<vir_low::Expression>,
        new_lifetime: vir_low::Expression,
        old_lifetime: vir_low::Expression,
        lifetime_permission_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;

    #[allow(clippy::too_many_arguments)]
    fn call_restore_raw_borrowed_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        borrowing_address: vir_low::Expression,
        restored_place: vir_low::Expression,
        restored_root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments;
}

impl<'p, 'v: 'p, 'tcx: 'v> BuiltinMethodCallsInterface for Lowerer<'p, 'v, 'tcx> {
    fn call_write_place_constant_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = BuiltinMethodCallBuilder::new(
            self,
            context,
            "write_place_constant",
            ty,
            generics,
            position,
        )?;
        builder.add_argument(target_place);
        builder.add_argument(target_address);
        builder.add_argument(source_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }

    fn call_move_place_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_root_address: vir_low::Expression,
        source_place: vir_low::Expression,
        source_root_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder =
            BuiltinMethodCallBuilder::new(self, context, "move_place", ty, generics, position)?;
        builder.add_argument(target_place);
        builder.add_argument(target_root_address);
        builder.add_argument(source_place);
        builder.add_argument(source_root_address);
        builder.add_argument(source_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }

    fn call_copy_place_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        target_place: vir_low::Expression,
        target_address: vir_low::Expression,
        source_place: vir_low::Expression,
        source_address: vir_low::Expression,
        source_snapshot: vir_low::Expression,
        source_permission_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder =
            BuiltinMethodCallBuilder::new(self, context, "copy_place", ty, generics, position)?;
        builder.add_argument(target_place);
        builder.add_argument(target_address);
        builder.add_argument(source_place);
        builder.add_argument(source_address);
        builder.add_argument(source_snapshot);
        builder.add_argument(source_permission_amount);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }

    fn call_into_memory_block_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        guard: Option<vir_low::Expression>,
        place: vir_low::Expression,
        address: vir_low::Expression,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = BuiltinMethodCallBuilder::new(
            self,
            context,
            "into_memory_block",
            ty,
            generics,
            position,
        )?;
        builder.add_argument(place);
        builder.add_argument(address);
        builder.add_argument(snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        builder.set_maybe_guard(guard);
        Ok(builder.build())
    }

    fn call_bor_shorten<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: Option<vir_low::Expression>,
        new_lifetime: vir_low::Expression,
        old_lifetime: vir_low::Expression,
        lifetime_permission_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder =
            BuiltinMethodCallBuilder::new(self, context, "bor_shorten", ty, generics, position)?;
        builder.add_argument(new_lifetime);
        builder.add_argument(old_lifetime);
        builder.add_argument(lifetime_permission_amount);
        builder.add_argument(place);
        builder.add_argument(root_address);
        builder.add_argument(current_snapshot);
        if let Some(final_snapshot) = final_snapshot {
            builder.add_argument(final_snapshot);
        }
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        Ok(builder.build())
    }

    fn call_restore_raw_borrowed_method<G>(
        &mut self,
        context: CallContext,
        ty: &vir_mid::Type,
        generics: &G,
        position: vir_low::Position,
        borrowing_address: vir_low::Expression,
        restored_place: vir_low::Expression,
        restored_root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Statement>
    where
        G: WithLifetimes + WithConstArguments,
    {
        let mut builder = BuiltinMethodCallBuilder::new(
            self,
            context,
            "restore_raw_borrowed",
            ty,
            generics,
            position,
        )?;
        builder.add_argument(borrowing_address);
        builder.add_argument(restored_place);
        builder.add_argument(restored_root_address);
        builder.add_argument(snapshot);
        Ok(builder.build())
    }
}
