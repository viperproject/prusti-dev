use super::{
    super::calls::builder::BuiltinMethodCallBuilder,
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
    move_copy_place_common::MoveCopyPlaceMethodBuilder,
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::{
            calls::interface::CallContext, BuiltinMethodCallsInterface, BuiltinMethodsInterface,
        },
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        references::ReferencesInterface,
        snapshots::SnapshotValuesInterface,
    },
};
use vir_crate::{
    common::expression::UnaryOperationHelpers,
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MovePlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: MoveCopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx>,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MovePlaceMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self.inner.inner.inner()
    }
}

impl<'l, 'p, 'v, 'tcx> MovePlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let inner =
            MoveCopyPlaceMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self { inner })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .inner
            .parameters
            .push(self.inner.target_place.clone());
        self.inner
            .inner
            .parameters
            .push(self.inner.target_address.clone());
        self.inner
            .inner
            .parameters
            .push(self.inner.source_place.clone());
        self.inner
            .inner
            .parameters
            .push(self.inner.source_address.clone());
        self.inner
            .inner
            .parameters
            .push(self.inner.source_snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn create_body(&mut self) {
        self.inner.create_body();
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.create_target_memory_block()
    }

    pub(in super::super::super::super) fn create_source_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_memory_block(
            self.inner.source_address.clone().into(), // self.compute_address(&self.inner.source_place, &self.inner.source_address),
        )
    }

    pub(in super::super::super::super) fn create_source_owned(
        &mut self,
        exclude_snapshot_equality: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .create_source_owned(exclude_snapshot_equality, None)
    }

    pub(in super::super::super::super) fn create_target_owned(
        &mut self,
        exclude_snapshot_equality: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.create_target_owned(exclude_snapshot_equality)
    }

    pub(in super::super::super::super) fn add_target_validity_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_target_validity_postcondition()
    }

    // // FIXME: Is this needed?
    // pub(in super::super::super::super) fn add_source_bytes_unchanged_postcondition(
    //     &mut self,
    // ) -> SpannedEncodingResult<()> {
    //     use vir_low::macros::*;
    //     let ty = self.inner.inner.ty;
    //     self.inner
    //         .inner
    //         .lowerer
    //         .encode_snapshot_to_bytes_function(ty)?;
    //     let to_bytes = ty! { Bytes };
    //     let size_of = self
    //         .inner
    //         .inner
    //         .lowerer
    //         .encode_type_size_expression2(self.inner.inner.ty, self.inner.inner.type_decl)?;
    //     let source_address =
    //         self.compute_address(&self.inner.source_place, &self.inner.source_address);
    //     let bytes = self
    //         .inner
    //         .inner
    //         .lowerer
    //         .encode_memory_block_bytes_expression(source_address, size_of)?;
    //     let expression = expr! {
    //         ([bytes] == (Snap<ty>::to_bytes([self.inner.source_snapshot.clone().into()])))
    //     };
    //     self.add_postcondition(expression);
    //     Ok(())
    // }

    pub(in super::super::super::super) fn add_statement(&mut self, statement: vir_low::Statement) {
        self.inner.add_statement(statement);
    }

    pub(in super::super::super::super) fn add_split_target_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_split_target_memory_block_call()
    }

    pub(in super::super::super::super) fn add_join_source_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_join_source_memory_block_call()
    }

    pub(in super::super::super::super) fn add_move_place_call_for_field(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .inner
            .lowerer
            .encode_move_place_method(&field.ty)?;
        let source_field_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            field,
            self.inner.source_place.clone().into(),
            self.inner.inner.position,
        )?;
        let source_field_address = self.inner.inner.lowerer.encode_field_address(
            self.inner.inner.ty,
            field,
            self.inner.source_address.clone().into(),
            self.inner.inner.position,
        )?;
        let target_field_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            field,
            self.inner.target_place.clone().into(),
            self.inner.inner.position,
        )?;
        let target_field_address = self.inner.inner.lowerer.encode_field_address(
            self.inner.inner.ty,
            field,
            self.inner.target_address.clone().into(),
            self.inner.inner.position,
        )?;
        let source_field_snapshot = self.inner.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.inner.ty,
            field,
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.position,
        )?;
        let statement = self.inner.inner.lowerer.call_move_place_method(
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            self.inner.inner.position,
            target_field_place,
            target_field_address,
            source_field_place,
            source_field_address,
            source_field_snapshot,
        )?;
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_move_place_call_for_variant(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let discriminant_call = self.inner.inner.lowerer.obtain_enum_discriminant(
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.ty,
            self.inner.inner.position,
        )?;
        let condition = expr! {
            [discriminant_call] == [discriminant_value.into()]
        };
        let variant_index = variant.name.clone().into();
        let target_variant_place = self.inner.inner.lowerer.encode_enum_variant_place(
            self.inner.inner.ty,
            &variant_index,
            self.inner.target_place.clone().into(),
            self.inner.inner.position,
        )?;
        let target_variant_address = self.inner.inner.lowerer.encode_enum_variant_address(
            self.inner.inner.ty,
            &variant_index,
            self.inner.target_address.clone().into(),
            self.inner.inner.position,
        )?;
        let source_variant_place = self.inner.inner.lowerer.encode_enum_variant_place(
            self.inner.inner.ty,
            &variant_index,
            self.inner.source_place.clone().into(),
            self.inner.inner.position,
        )?;
        let source_variant_address = self.inner.inner.lowerer.encode_enum_variant_address(
            self.inner.inner.ty,
            &variant_index,
            self.inner.source_address.clone().into(),
            self.inner.inner.position,
        )?;
        let source_variant_snapshot = self.inner.inner.lowerer.obtain_enum_variant_snapshot(
            self.inner.inner.ty,
            &variant_index,
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.position,
        )?;
        let variant_ty = self.inner.inner.ty.clone().variant(variant_index);
        self.inner
            .inner
            .lowerer
            .encode_move_place_method(&variant_ty)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.inner.lowerer,
            CallContext::BuiltinMethod,
            "move_place",
            &variant_ty,
            variant,
            self.inner.inner.position,
        )?;
        builder.set_guard(condition);
        builder.add_argument(target_variant_place);
        builder.add_argument(target_variant_address);
        builder.add_argument(source_variant_place);
        builder.add_argument(source_variant_address);
        builder.add_argument(source_variant_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_move_place_call_for_discriminant(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<()> {
        let discriminant_field = decl.discriminant_field();
        self.inner
            .inner
            .lowerer
            .encode_move_place_method(&discriminant_field.ty)?;
        let discriminant_call = self.inner.inner.lowerer.obtain_enum_discriminant(
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.ty,
            self.inner.inner.position,
        )?;
        let target_discriminant_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            &discriminant_field,
            self.inner.target_place.clone().into(),
            self.inner.inner.position,
        )?;
        let target_discriminant_address = self.inner.inner.lowerer.encode_field_address(
            self.inner.inner.ty,
            &discriminant_field,
            self.inner.target_address.clone().into(),
            self.inner.inner.position,
        )?;
        let source_discriminant_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            &discriminant_field,
            self.inner.source_place.clone().into(),
            self.inner.inner.position,
        )?;
        let source_discriminant_address = self.inner.inner.lowerer.encode_field_address(
            self.inner.inner.ty,
            &discriminant_field,
            self.inner.source_address.clone().into(),
            self.inner.inner.position,
        )?;
        let source_discriminant_snashot = self.inner.inner.lowerer.construct_constant_snapshot(
            &decl.discriminant_type,
            discriminant_call,
            self.inner.inner.position,
        )?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.inner.lowerer,
            CallContext::BuiltinMethod,
            "move_place",
            &decl.discriminant_type,
            &decl.discriminant_type,
            self.inner.inner.position,
        )?;
        builder.add_argument(target_discriminant_place);
        builder.add_argument(target_discriminant_address);
        builder.add_argument(source_discriminant_place);
        builder.add_argument(source_discriminant_address);
        builder.add_argument(source_discriminant_snashot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_memory_block_copy_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_memory_block_copy_call(None)
    }

    pub(in super::super::super::super) fn change_unique_ref_place(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .inner
            .lowerer
            .encode_change_unique_ref_place_method(self.inner.inner.ty)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.inner.lowerer,
            CallContext::BuiltinMethod,
            "change_unique_ref_place",
            self.inner.inner.ty,
            self.inner.inner.type_decl,
            self.inner.inner.position,
        )?;
        builder.add_argument(self.inner.target_place.clone().into());
        builder.add_argument(self.inner.source_place.clone().into());
        builder.add_argument(self.inner.source_snapshot.clone().into());
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_dead_lifetime_hack(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let lifetime_alive = self
            .inner
            .inner
            .lowerer
            .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
        let guard = vir_low::Expression::not(lifetime_alive.into());
        let source_current_snapshot = self.inner.inner.lowerer.reference_target_current_snapshot(
            self.inner.inner.ty,
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.position,
        )?;
        let source_final_snapshot = self.inner.inner.lowerer.reference_target_final_snapshot(
            self.inner.inner.ty,
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.position,
        )?;
        let target_snapshot = self.inner.inner.lowerer.owned_non_aliased_snap(
            CallContext::BuiltinMethod,
            self.inner.inner.ty,
            self.inner.inner.type_decl,
            self.inner.target_place.clone().into(),
            self.inner.target_address.clone().into(),
            self.inner.inner.position,
        )?;
        let target_current_snapshot = self.inner.inner.lowerer.reference_target_current_snapshot(
            self.inner.inner.ty,
            target_snapshot.clone(),
            self.inner.inner.position,
        )?;
        let target_final_snapshot = self.inner.inner.lowerer.reference_target_final_snapshot(
            self.inner.inner.ty,
            target_snapshot,
            self.inner.inner.position,
        )?;
        let body = vec![
            vir_low::Statement::comment(
                "FIXME: This is a hack. Because the lifetime is dead, the reference \
                is dangling and there is no predicate that would witness that \
                the value of the dereference is the source of the dereference. \
                This is also the reason why it is sound just to assume that the \
                two are equal. A proper solution should use a custom equality function \
                that equates the targets only if lifetimes are alive."
                    .to_string(),
            ),
            stmtp! { self.inner.inner.position =>
                assume ([source_current_snapshot] == [target_current_snapshot])
            },
            stmtp! { self.inner.inner.position =>
                assume ([source_final_snapshot] == [target_final_snapshot])
            },
            //             assume destructor$Snap$ref$Unique$slice$struct$m_T1$$$target_current(source_snapshot) == destructor$Snap$ref$Unique$slice$struct$m_T1$$$target_current(snap_owned_non_aliased$ref$Unique$slice$struct$m_T1$(target_place, target_address, lft_early_bound_0$alive, lft_early_bound_0))

            // assume destructor$Snap$ref$Unique$slice$struct$m_T1$$$target_final(source_snapshot) == destructor$Snap$ref$Unique$slice$struct$m_T1$$$target_final(snap_owned_non_aliased$ref$Unique$slice$struct$m_T1$(target_place, target_address, lft_early_bound_0$alive, lft_early_bound_0))
        ];
        let statement =
            vir_low::Statement::conditional(guard, body, Vec::new(), self.inner.inner.position);
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn duplicate_frac_ref(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        self.inner.duplicate_frac_ref(lifetime, None)
        // self.inner
        //     .inner
        //     .lowerer
        //     .encode_duplicate_frac_ref_method(self.inner.inner.ty)?;
        // let mut builder = BuiltinMethodCallBuilder::new(
        //     self.inner.inner.lowerer,
        //     CallContext::BuiltinMethod,
        //     "duplicate_frac_ref",
        //     self.inner.inner.ty,
        //     self.inner.inner.type_decl,
        //     self.inner.inner.position,
        // )?;
        // builder.add_argument(self.inner.target_place.clone().into());
        // builder.add_argument(self.inner.source_place.clone().into());
        // builder.add_argument(self.inner.source_snapshot.clone().into());
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let statement = builder.build();
        // self.add_statement(statement);
        // Ok(())
    }
}
