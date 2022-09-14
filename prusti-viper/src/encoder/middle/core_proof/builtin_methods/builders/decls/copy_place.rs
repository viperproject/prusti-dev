use super::{
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
    move_copy_place_common::MoveCopyPlaceMethodBuilder,
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        builtin_methods::{BuiltinMethodCallsInterface, BuiltinMethodsInterface, CallContext},
        lowerer::Lowerer,
        places::PlacesInterface,
        snapshots::SnapshotValuesInterface,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct CopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: MoveCopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx>,
    source_permission_amount: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for CopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self.inner.inner()
    }
}

impl<'l, 'p, 'v, 'tcx> CopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let source_permission_amount =
            vir_low::VariableDecl::new("source_permission_amount", vir_low::Type::Perm);
        let inner =
            MoveCopyPlaceMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            source_permission_amount,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
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
        self.inner
            .inner
            .parameters
            .push(self.source_permission_amount.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn add_permission_amount_positive_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self
            .inner
            .create_permission_amount_positive(&self.source_permission_amount)?;
        self.add_precondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.create_target_memory_block()
    }

    pub(in super::super::super::super) fn create_source_owned(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .create_source_owned(false, Some(self.source_permission_amount.clone().into()))
        // self.inner.inner.lowerer.owned_non_aliased(
        //     CallContext::BuiltinMethod,
        //     self.inner.inner.ty,
        //     self.inner.inner.type_decl,
        //     self.inner.source_place.clone().into(),
        //     self.inner.source_address.clone().into(),
        //     Some(self.source_permission_amount.clone().into()),
        //     self.inner.inner.position,
        // )
    }

    pub(in super::super::super::super) fn create_source_owned_predicate(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner
            .create_source_owned(true, Some(self.source_permission_amount.clone().into()))
        // self.inner.inner.lowerer.owned_non_aliased(
        //     CallContext::BuiltinMethod,
        //     self.inner.inner.ty,
        //     self.inner.inner.type_decl,
        //     self.inner.source_place.clone().into(),
        //     self.inner.source_address.clone().into(),
        //     Some(self.source_permission_amount.clone().into()),
        //     self.inner.inner.position,
        // )
    }

    pub(in super::super::super::super) fn create_target_owned(
        &mut self,
        must_be_predicate: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.create_target_owned(must_be_predicate)
    }

    pub(in super::super::super::super) fn add_target_validity_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_target_validity_postcondition()
    }

    pub(in super::super::super::super) fn add_statement(&mut self, statement: vir_low::Statement) {
        self.inner.add_statement(statement);
    }

    pub(in super::super::super::super) fn add_memory_block_copy_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .add_memory_block_copy_call(Some(self.source_permission_amount.clone().into()))
    }

    pub(in super::super::super::super) fn add_split_target_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_split_target_memory_block_call()
    }

    pub(in super::super::super::super) fn add_copy_place_call_for_field(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .inner
            .lowerer
            .encode_copy_place_method(&field.ty)?;
        let source_field_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            field,
            self.inner.source_place.clone().into(),
            self.inner.inner.position,
        )?;
        let target_field_place = self.inner.inner.lowerer.encode_field_place(
            self.inner.inner.ty,
            field,
            self.inner.target_place.clone().into(),
            self.inner.inner.position,
        )?;
        let source_field_snapshot = self.inner.inner.lowerer.obtain_struct_field_snapshot(
            self.inner.inner.ty,
            field,
            self.inner.source_snapshot.clone().into(),
            self.inner.inner.position,
        )?;
        let statement = self.inner.inner.lowerer.call_copy_place_method(
            CallContext::BuiltinMethod,
            &field.ty,
            &field.ty,
            self.inner.inner.position,
            target_field_place,
            self.inner.target_address.clone().into(),
            source_field_place,
            self.inner.source_address.clone().into(),
            source_field_snapshot,
            self.source_permission_amount.clone().into(),
        )?;
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn duplicate_frac_ref(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .duplicate_frac_ref(lifetime, Some(self.source_permission_amount.clone().into()))
    }
}
