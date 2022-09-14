use super::{
    super::calls::builder::BuiltinMethodCallBuilder,
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::{BuiltinMethodsInterface, CallContext},
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{IntoSnapshot, SnapshotValidityInterface, SnapshotValuesInterface},
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct WritePlaceConstantMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    target_place: vir_low::VariableDecl,
    target_address: vir_low::VariableDecl,
    source_snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for WritePlaceConstantMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> WritePlaceConstantMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let target_place = vir_low::VariableDecl::new("target_place", lowerer.place_option_type()?);
        let target_address = vir_low::VariableDecl::new("target_address", lowerer.address_type()?);
        let source_snapshot =
            vir_low::VariableDecl::new("source_snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            target_place,
            target_address,
            source_snapshot,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.target_place.clone());
        self.inner.parameters.push(self.target_address.clone());
        self.inner.parameters.push(self.source_snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn create_body(&mut self) {
        debug_assert!(
            self.inner.statements.is_none(),
            "The body is already created."
        );
        self.inner.statements = Some(Vec::new());
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_memory_block(
            self.target_address.clone().into(),
            // self.compute_address(&self.target_place, &self.target_address),
        )
    }

    // FIXME: Remove duplicates with other builders.
    pub(in super::super::super::super) fn create_target_owned(
        &mut self,
        exclude_snapshot_equality: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if exclude_snapshot_equality {
            self.inner.lowerer.owned_non_aliased_full_vars(
                CallContext::BuiltinMethod,
                self.inner.ty,
                self.inner.type_decl,
                &self.target_place,
                &self.target_address,
                self.inner.position,
            )
        } else {
            self.inner
                .lowerer
                .owned_non_aliased_full_vars_with_snapshot(
                    CallContext::BuiltinMethod,
                    self.inner.ty,
                    self.inner.type_decl,
                    &self.target_place,
                    &self.target_address,
                    &self.source_snapshot,
                    self.inner.position,
                )
        }
        // self.inner
        //     .lowerer
        //     .mark_owned_predicate_as_unfolded(self.inner.ty)?;
        // self.inner.lowerer.owned_non_aliased_full_vars(
        //     CallContext::BuiltinMethod,
        //     self.inner.ty,
        //     self.inner.type_decl,
        //     &self.target_place,
        //     &self.target_address,
        //     self.inner.position,
        // )
    }

    pub(in super::super::super::super) fn add_source_validity_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let validity = self.inner.lowerer.encode_snapshot_valid_call_for_type(
            self.source_snapshot.clone().into(),
            self.inner.ty,
        )?;
        self.add_precondition(validity);
        Ok(())
    }

    // FIXME: Remove code duplication.
    pub(in super::super::super::super) fn add_statement(&mut self, statement: vir_low::Statement) {
        self.inner
            .statements
            .as_mut()
            .unwrap()
            .push(statement.set_default_position(self.inner.position));
    }

    // FIXME: Remove code duplication.
    fn discriminant(&mut self) -> SpannedEncodingResult<Option<vir_low::Expression>> {
        if self.inner.ty.has_variants() {
            Ok(Some(self.inner.lowerer.obtain_enum_discriminant(
                self.source_snapshot.clone().into(),
                self.inner.ty,
                self.inner.position,
            )?))
        } else {
            Ok(None)
        }
    }

    // FIXME: Remove code duplication.
    pub(in super::super::super::super) fn add_split_target_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_memory_block_split_method(self.inner.ty)?;
        // let target_address = self.compute_address(&self.target_place, &self.target_address);
        let discriminant_call = self.discriminant()?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "memory_block_split",
            self.inner.ty,
            self.inner.type_decl,
            self.inner.position,
        )?;
        builder.add_argument(self.target_address.clone().into());
        builder.add_full_permission_argument();
        if let Some(discriminant_call) = discriminant_call {
            builder.add_argument(discriminant_call);
        }
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_write_constant_call_for_field(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_write_place_constant_method(&field.ty)?;
        let target_field_place = self.inner.lowerer.encode_field_place(
            self.inner.ty,
            field,
            self.target_place.clone().into(),
            self.inner.position,
        )?;
        let target_field_address = self.inner.lowerer.encode_field_address(
            self.inner.ty,
            field,
            self.target_address.clone().into(),
            self.inner.position,
        )?;
        let source_field_snapshot = self.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.ty,
            field,
            self.source_snapshot.clone().into(),
            self.inner.position,
        )?;
        self.inner.lowerer.encode_move_place_method(&field.ty)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "write_place_constant",
            &field.ty,
            &field.ty,
            self.inner.position,
        )?;
        builder.add_argument(target_field_place);
        builder.add_argument(target_field_address);
        builder.add_argument(source_field_snapshot);
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_write_address_constant_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_write_address_constant_method(self.inner.ty)?;
        // let address = self.compute_address(&self.target_place, &self.target_address);
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "write_address_constant",
            self.inner.ty,
            self.inner.type_decl,
            self.inner.position,
        )?;
        builder.add_argument(self.target_address.clone().into());
        builder.add_argument(self.source_snapshot.clone().into());
        builder.add_lifetime_arguments()?;
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }
}
