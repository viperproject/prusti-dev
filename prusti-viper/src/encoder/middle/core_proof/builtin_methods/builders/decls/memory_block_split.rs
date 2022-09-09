use super::{
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
    memory_block_split_join_common::{
        BuiltinMethodSplitJoinBuilderMethods, MemoryBlockSplitJoinMethodBuilder,
    },
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        lowerer::Lowerer, predicates::PredicatesMemoryBlockInterface, snapshots::IntoSnapshot,
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::ExpressionIterator,
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MemoryBlockSplitMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: MemoryBlockSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx>,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockSplitMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self.inner.inner()
    }
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodSplitJoinBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockSplitMethodBuilder<'l, 'p, 'v, 'tcx>
{
}

impl<'l, 'p, 'v, 'tcx> MemoryBlockSplitMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            inner: MemoryBlockSplitJoinMethodBuilder::new(
                lowerer,
                kind,
                method_name,
                ty,
                type_decl,
                error_kind,
            )?,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.create_parameters()
    }

    pub(in super::super::super::super) fn add_permission_amount_positive_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_permission_amount_positive_precondition()
    }

    pub(in super::super::super::super) fn add_whole_memory_block_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let memory_block = self.inner.create_whole_block_acc()?;
        self.add_precondition(memory_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_padding_memory_block_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self.inner.create_padding_memory_block_acc()?;
        self.add_postcondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_field_memory_block_postcondition(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        let field_block = self.inner.create_field_memory_block_acc(field)?;
        self.add_postcondition(field_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_discriminant_postcondition(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<()> {
        let discriminant_block = self.inner.create_discriminant_acc(decl)?;
        self.add_postcondition(discriminant_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_variant_memory_block_postcondition(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        let expression = self
            .inner
            .create_variant_memory_block_acc(discriminant_value, variant)?;
        self.add_postcondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn create_field_to_bytes_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.create_field_to_bytes_equality(field)
    }

    pub(in super::super::super::super) fn add_fields_to_bytes_equalities_postcondition(
        &mut self,
        field_to_bytes_equalities: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let address = self.inner.address();
        let inner = self.inner();
        let to_bytes = ty! { Bytes };
        let ty = inner.ty;
        let size_of = inner
            .lowerer
            .encode_type_size_expression2(inner.ty, inner.type_decl)?;
        let memory_block_bytes = inner
            .lowerer
            .encode_memory_block_bytes_expression(address, size_of)?;
        let bytes_quantifier = expr! {
            forall(
                snapshot: {ty.to_snapshot(inner.lowerer)?} ::
                [ { (Snap<ty>::to_bytes(snapshot)) } ]
                ((old([memory_block_bytes])) == (Snap<ty>::to_bytes(snapshot))) ==>
                [ field_to_bytes_equalities.into_iter().conjoin() ]
            )
        };
        self.add_postcondition(bytes_quantifier);
        Ok(())
    }
}
