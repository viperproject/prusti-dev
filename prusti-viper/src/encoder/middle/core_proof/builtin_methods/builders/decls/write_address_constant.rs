use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer, snapshots::IntoSnapshot,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct WriteAddressConstantMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    target_address: vir_low::VariableDecl,
    source_snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for WriteAddressConstantMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> WriteAddressConstantMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let target_address = vir_low::VariableDecl::new("target_address", lowerer.address_type()?);
        let source_snapshot =
            vir_low::VariableDecl::new("source_snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
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
        self.inner.parameters.push(self.target_address.clone());
        self.inner.parameters.push(self.source_snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn create_target_memory_block(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.create_memory_block(self.target_address.clone().into())
    }

    pub(in super::super::super::super) fn add_target_snapshot_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let target_bytes = self
            .inner
            .create_memory_block_bytes(self.target_address.clone().into())?;
        let ty = self.inner.ty;
        let to_bytes = ty! { Bytes };
        let expression = expr! {
            [target_bytes] == (Snap<ty>::to_bytes([self.source_snapshot.clone().into()]))
        };
        self.add_postcondition(expression);
        Ok(())
    }
}
