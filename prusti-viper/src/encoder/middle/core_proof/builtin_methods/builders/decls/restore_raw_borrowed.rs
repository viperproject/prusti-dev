use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::{PredicatesOwnedInterface, RestorationInterface},
        snapshots::IntoSnapshot,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct RestoreRawBorrowedMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    borrowing_address: vir_low::VariableDecl,
    restored_place: vir_low::VariableDecl,
    restored_root_address: vir_low::VariableDecl,
    snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for RestoreRawBorrowedMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> RestoreRawBorrowedMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let borrowing_address =
            vir_low::VariableDecl::new("borrowing_address", lowerer.address_type()?);
        let restored_place = vir_low::VariableDecl::new("restored_place", lowerer.place_type()?);
        let restored_root_address =
            vir_low::VariableDecl::new("restored_root_address", lowerer.address_type()?);
        let snapshot = vir_low::VariableDecl::new("snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            borrowing_address,
            restored_place,
            restored_root_address,
            snapshot,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.borrowing_address.clone());
        self.inner.parameters.push(self.restored_place.clone());
        self.inner
            .parameters
            .push(self.restored_root_address.clone());
        self.inner.parameters.push(self.snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn add_aliased_source_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let _aliased_root_place = self
            .inner
            .lowerer
            .encode_aliased_place_root(self.inner.position)?;
        unimplemented!();
        // let aliased_predicate = self.inner.lowerer.owned_aliased(
        //     CallContext::BuiltinMethod,
        //     self.inner.ty,
        //     self.inner.ty,
        //     aliased_root_place,
        //     self.borrowing_address.clone().into(),
        //     self.snapshot.clone().into(),
        //     None,
        // )?;
        // self.add_precondition(aliased_predicate);
        Ok(())
    }

    pub(in super::super::super::super) fn add_shift_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let restore_raw_borrowed = self.inner.lowerer.restore_raw_borrowed(
            self.inner.ty,
            self.restored_place.clone().into(),
            self.restored_root_address.clone().into(),
        )?;
        self.add_precondition(restore_raw_borrowed);
        Ok(())
    }

    pub(crate) fn add_non_aliased_target_postcondition(&mut self) -> SpannedEncodingResult<()> {
        let non_aliased_predicate = self
            .inner
            .lowerer
            .owned_non_aliased_full_vars_with_snapshot(
                CallContext::BuiltinMethod,
                self.inner.ty,
                self.inner.ty,
                &self.restored_place,
                &self.restored_root_address,
                &self.snapshot,
                self.inner.position,
            )?;
        self.add_postcondition(non_aliased_predicate);
        Ok(())
    }
}
