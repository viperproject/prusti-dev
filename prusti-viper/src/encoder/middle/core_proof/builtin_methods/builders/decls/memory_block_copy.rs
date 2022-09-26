use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{addresses::AddressesInterface, lowerer::Lowerer},
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MemoryBlockCopyMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    source_address: vir_low::VariableDecl,
    target_address: vir_low::VariableDecl,
    permission_amount: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockCopyMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> MemoryBlockCopyMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let source_address = vir_low::VariableDecl::new("source_address", lowerer.address_type()?);
        let target_address = vir_low::VariableDecl::new("target_address", lowerer.address_type()?);
        let permission_amount =
            vir_low::VariableDecl::new("permission_amount", vir_low::Type::Perm);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            source_address,
            target_address,
            permission_amount,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.source_address.clone());
        self.inner.parameters.push(self.target_address.clone());
        self.inner.parameters.push(self.permission_amount.clone());
        // Lifetimes skipped because size should not depend on them.
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn add_permission_amount_positive_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self
            .inner
            .create_permission_amount_positive(&self.permission_amount)?;
        self.add_precondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_target_invariant(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self.create_memory_block(self.target_address.clone().into())?;
        self.add_precondition(expression.clone());
        self.add_postcondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_source_invariant(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self.create_memory_block_with_permission_amount(
            self.source_address.clone().into(),
            self.permission_amount.clone().into(),
        )?;
        self.add_precondition(expression.clone());
        self.add_postcondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_target_is_source_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let target_bytes = self
            .inner
            .create_memory_block_bytes(self.target_address.clone().into())?;
        let source_bytes = self
            .inner
            .create_memory_block_bytes(self.source_address.clone().into())?;
        let expression = expr! {
            [target_bytes] == [source_bytes]
        };
        self.add_postcondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_source_preserved_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let source_bytes = self
            .inner
            .create_memory_block_bytes(self.source_address.clone().into())?;
        let expression = expr! {
            [source_bytes.clone()] == (old([source_bytes]))
        };
        self.add_postcondition(expression);
        Ok(())
    }
}
