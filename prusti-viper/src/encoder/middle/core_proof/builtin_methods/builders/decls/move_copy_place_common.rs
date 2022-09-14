use super::{
    super::calls::builder::BuiltinMethodCallBuilder,
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::{calls::interface::CallContext, BuiltinMethodsInterface},
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        snapshots::{IntoSnapshot, SnapshotValidityInterface},
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MoveCopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(super) inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    pub(super) target_place: vir_low::VariableDecl,
    pub(super) target_root_address: vir_low::VariableDecl,
    pub(super) source_place: vir_low::VariableDecl,
    pub(super) source_root_address: vir_low::VariableDecl,
    pub(super) source_snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MoveCopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> MoveCopyPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let target_place = vir_low::VariableDecl::new("target_place", lowerer.place_type()?);
        let target_root_address =
            vir_low::VariableDecl::new("target_root_address", lowerer.address_type()?);
        let source_place = vir_low::VariableDecl::new("source_place", lowerer.place_type()?);
        let source_root_address =
            vir_low::VariableDecl::new("source_root_address", lowerer.address_type()?);
        let source_snapshot =
            vir_low::VariableDecl::new("source_snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            target_place,
            target_root_address,
            source_place,
            source_root_address,
            source_snapshot,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_memory_block(
            self.compute_address(&self.target_place, &self.target_root_address),
        )
    }

    pub(in super::super::super::super) fn create_source_owned(
        &mut self,
        must_be_predicate: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.lowerer.owned_non_aliased_full_vars(
            CallContext::BuiltinMethod,
            self.inner.ty,
            self.inner.type_decl,
            &self.source_place,
            &self.source_root_address,
            &self.source_snapshot,
            must_be_predicate,
        )
    }

    // FIXME: Remove duplicates with other builders.
    pub(in super::super::super::super) fn create_target_owned(
        &mut self,
        must_be_predicate: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.lowerer.owned_non_aliased_full_vars(
            CallContext::BuiltinMethod,
            self.inner.ty,
            self.inner.type_decl,
            &self.target_place,
            &self.target_root_address,
            &self.source_snapshot,
            must_be_predicate,
        )
    }

    // FIXME: Remove duplicate with add_source_validity_precondition
    pub(in super::super::super::super) fn add_target_validity_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let validity = self.inner.lowerer.encode_snapshot_valid_call_for_type(
            self.source_snapshot.clone().into(),
            self.inner.ty,
        )?;
        self.add_postcondition(validity);
        Ok(())
    }

    pub(in super::super::super::super) fn add_memory_block_copy_call(
        &mut self,
        source_permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_memory_block_copy_method(self.inner.ty)?;
        let source_address = self.compute_address(&self.source_place, &self.source_root_address);
        let target_address = self.compute_address(&self.target_place, &self.target_root_address);
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "memory_copy",
            self.inner.ty,
            self.inner.type_decl,
            self.inner.position,
        )?;
        builder.add_argument(source_address);
        builder.add_argument(target_address);
        if let Some(source_permission_amount) = source_permission_amount {
            builder.add_argument(source_permission_amount);
        } else {
            builder.add_argument(vir_low::Expression::full_permission());
        }
        builder.add_const_arguments()?;
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_split_target_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_memory_block_split_method(self.inner.ty)?;
        let target_address = self.compute_address(&self.target_place, &self.target_root_address);
        let discriminant_call = self.inner.discriminant(&self.source_snapshot)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "memory_block_split",
            self.inner.ty,
            self.inner.type_decl,
            self.inner.position,
        )?;
        builder.add_argument(target_address);
        builder.add_full_permission_argument();
        if let Some(discriminant_call) = discriminant_call {
            builder.add_argument(discriminant_call);
        }
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }

    pub(in super::super::super::super) fn add_join_source_memory_block_call(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner
            .lowerer
            .encode_memory_block_join_method(self.inner.ty)?;
        let source_address = self.compute_address(&self.source_place, &self.source_root_address);
        let discriminant_call = self.inner.discriminant(&self.source_snapshot)?;
        let mut builder = BuiltinMethodCallBuilder::new(
            self.inner.lowerer,
            CallContext::BuiltinMethod,
            "memory_block_join",
            self.inner.ty,
            self.inner.type_decl,
            self.inner.position,
        )?;
        builder.add_argument(source_address);
        builder.add_full_permission_argument();
        if let Some(discriminant_call) = discriminant_call {
            builder.add_argument(discriminant_call);
        }
        let statement = builder.build();
        self.add_statement(statement);
        Ok(())
    }
}
