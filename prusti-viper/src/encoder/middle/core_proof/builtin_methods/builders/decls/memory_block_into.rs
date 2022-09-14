use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::{
            builders::calls::builder::BuiltinMethodCallBuilder, calls::interface::CallContext,
            BuiltinMethodsInterface,
        },
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{IntoSnapshot, SnapshotValuesInterface},
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct IntoMemoryBlockMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    place: vir_low::VariableDecl,
    address: vir_low::VariableDecl,
    snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for IntoMemoryBlockMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> IntoMemoryBlockMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let place = vir_low::VariableDecl::new("place", lowerer.place_option_type()?);
        let address = vir_low::VariableDecl::new("address", lowerer.address_type()?);
        let snapshot = vir_low::VariableDecl::new("snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            place,
            address,
            snapshot,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.place.clone());
        self.inner.parameters.push(self.address.clone());
        self.inner.parameters.push(self.snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    // FIXME: Remove code duplication with create_source_owned.
    pub(in super::super::super::super) fn create_owned(
        &mut self,
        exclude_snapshot_equality: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if exclude_snapshot_equality {
            self.inner.lowerer.owned_non_aliased_full_vars(
                CallContext::BuiltinMethod,
                self.inner.ty,
                self.inner.type_decl,
                &self.place,
                &self.address,
                self.inner.position,
            )
        } else {
            self.inner
                .lowerer
                .owned_non_aliased_full_vars_with_snapshot(
                    CallContext::BuiltinMethod,
                    self.inner.ty,
                    self.inner.type_decl,
                    &self.place,
                    &self.address,
                    &self.snapshot,
                    self.inner.position,
                )
        }
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // self.create_memory_block(self.compute_address(&self.place, &self.address))
        self.create_memory_block(self.address.clone().into())
    }

    pub(in super::super::super::super) fn add_into_memory_block_call_for_field(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        let field_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            field,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let field_address = self.inner.lowerer.encode_field_address(
            self.inner.ty,
            field,
            self.address.clone().into(),
            self.inner.position,
        )?;
        let field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.ty,
            field,
            self.snapshot.clone().into(),
            self.inner.position,
        )?;
        self.inner
            .lowerer
            .encode_into_memory_block_method(&field.ty)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "into_memory_block",
            &field.ty,
            &field.ty,
            self.inner.position,
        )?;
        builder.add_argument(field_place);
        builder.add_argument(field_address);
        builder.add_argument(field_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_into_memory_block_call_for_variant(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let condition = expr! {
            [discriminant_call] == [discriminant_value.into()]
        };
        let variant_index = variant.name.clone().into();
        let variant_place = self.inner.lowerer.encode_enum_variant_place(
            self.inner.ty,
            &variant_index,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let variant_address = self.inner.lowerer.encode_enum_variant_address(
            self.inner.ty,
            &variant_index,
            self.address.clone().into(),
            self.inner.position,
        )?;
        let variant_snapshot = self.inner.lowerer.obtain_enum_variant_snapshot(
            self.inner.ty,
            &variant_index,
            self.snapshot.clone().into(),
            self.inner.position,
        )?;
        let variant_ty = self.inner.ty.clone().variant(variant_index);
        self.inner
            .lowerer
            .encode_into_memory_block_method(&variant_ty)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "into_memory_block",
            &variant_ty,
            variant,
            self.inner.position,
        )?;
        builder.add_argument(variant_place);
        builder.add_argument(variant_address);
        builder.add_argument(variant_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        let statement =
            vir_low::Statement::conditional_no_pos(condition, vec![statement], Vec::new());
        self.add_statement(statement.set_default_position(self.inner.position));
        Ok(())
    }

    pub(in super::super::super::super) fn add_into_memory_block_call_for_discriminant(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<()> {
        let discriminant_field = decl.discriminant_field();
        self.inner
            .lowerer
            .encode_into_memory_block_method(&discriminant_field.ty)?;
        let discriminant_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            &discriminant_field,
            self.place.clone().into(),
            self.inner.position,
        )?;
        let discriminant_address = self.inner.lowerer.encode_field_address(
            self.inner.ty,
            &discriminant_field,
            self.address.clone().into(),
            self.inner.position,
        )?;
        let discriminant_call = self.inner.lowerer.obtain_enum_discriminant(
            self.snapshot.clone().into(),
            self.inner.ty,
            self.inner.position,
        )?;
        let discriminant_snashot = self.inner.lowerer.construct_constant_snapshot(
            &decl.discriminant_type,
            discriminant_call,
            self.inner.position,
        )?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "into_memory_block",
            &decl.discriminant_type,
            &decl.discriminant_type,
            self.inner.position,
        )?;
        builder.add_argument(discriminant_place);
        builder.add_argument(discriminant_address);
        builder.add_argument(discriminant_snashot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_join_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_join_memory_block_call(&self.place, &self.address, &self.snapshot)
    }
}
