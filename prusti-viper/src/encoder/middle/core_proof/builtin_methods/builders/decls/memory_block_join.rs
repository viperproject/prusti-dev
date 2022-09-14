use super::{
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
    memory_block_split_join_common::{
        BuiltinMethodSplitJoinBuilderMethods, MemoryBlockSplitJoinMethodBuilder,
    },
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::Lowerer,
        predicates::PredicatesMemoryBlockInterface,
        snapshots::{IntoSnapshot, SnapshotValuesInterface},
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::ExpressionIterator,
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MemoryBlockJoinMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: MemoryBlockSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx>,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockJoinMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self.inner.inner()
    }
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodSplitJoinBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockJoinMethodBuilder<'l, 'p, 'v, 'tcx>
{
}

impl<'l, 'p, 'v, 'tcx> MemoryBlockJoinMethodBuilder<'l, 'p, 'v, 'tcx> {
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

    pub(in super::super::super::super) fn add_whole_memory_block_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let memory_block = self.inner.create_whole_block_acc()?;
        self.add_postcondition(memory_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_padding_memory_block_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self.inner.create_padding_memory_block_acc()?;
        self.add_precondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn add_field_memory_block_precondition(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<()> {
        let field_block = self.inner.create_field_memory_block_acc(field)?;
        self.add_precondition(field_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_discriminant_precondition(
        &mut self,
        decl: &vir_mid::type_decl::Enum,
    ) -> SpannedEncodingResult<()> {
        let discriminant_block = self.inner.create_discriminant_acc(decl)?;
        self.add_precondition(discriminant_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_variant_memory_block_precondition(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
    ) -> SpannedEncodingResult<()> {
        let expression = self
            .inner
            .create_variant_memory_block_acc(discriminant_value, variant)?;
        self.add_precondition(expression);
        Ok(())
    }

    pub(in super::super::super::super) fn create_field_to_bytes_equality(
        &mut self,
        field: &vir_mid::FieldDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let expression = self.inner.create_field_to_bytes_equality(field)?;
        Ok(vir_low::Expression::labelled_old_no_pos(None, expression))
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
                [ field_to_bytes_equalities.into_iter().conjoin() ] ==>
                ([memory_block_bytes] == (Snap<ty>::to_bytes(snapshot)))
            )
        };
        self.add_postcondition(bytes_quantifier);
        Ok(())
    }

    pub(in super::super::super::super) fn create_variant_to_bytes_equality(
        &mut self,
        discriminant_value: vir_mid::DiscriminantValue,
        variant: &vir_mid::type_decl::Struct,
        decl: &vir_mid::type_decl::Enum,
        safety: vir_mid::ty::EnumSafety,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let discriminant = self.inner.discriminant.as_ref().unwrap();
        let ty = self.inner.inner.ty;
        let to_bytes = ty! { Bytes };
        let snapshot: vir_low::Expression =
            var! { snapshot: {self.inner.inner.ty.to_snapshot(self.inner.inner.lowerer)?} }.into();
        let variant_index = variant.name.clone().into();
        let variant_snapshot = self.inner.inner.lowerer.obtain_enum_variant_snapshot(
            ty,
            &variant_index,
            snapshot.clone(),
            self.inner.inner.position,
        )?;
        let variant_address = self.inner.inner.lowerer.encode_enum_variant_address(
            self.inner.inner.ty,
            &variant_index,
            self.inner.address.clone().into(),
            self.inner.inner.position,
        )?;
        let variant_type = &self.inner.inner.ty.clone().variant(variant_index);
        let variant_size_of = self
            .inner
            .inner
            .lowerer
            .encode_type_size_expression2(variant_type, variant)?;
        let memory_block_variant_bytes = self
            .inner
            .inner
            .lowerer
            .encode_memory_block_bytes_expression(variant_address, variant_size_of)?;
        let memory_block_bytes = self
            .inner
            .inner
            .create_memory_block_bytes(self.inner.address.clone().into())?;
        let discriminant_to_bytes = if safety.is_enum() {
            let discriminant_type = &decl.discriminant_type;
            let discriminant_size_of = self
                .inner
                .inner
                .lowerer
                .encode_type_size_expression2(&decl.discriminant_type, &decl.discriminant_type)?;
            let discriminant_field = decl.discriminant_field();
            let discriminant_address = self.inner.inner.lowerer.encode_field_address(
                self.inner.inner.ty,
                &discriminant_field,
                self.inner.address.clone().into(),
                self.inner.inner.position,
            )?;
            let memory_block_discriminant_bytes = self
                .inner
                .inner
                .lowerer
                .encode_memory_block_bytes_expression(discriminant_address, discriminant_size_of)?;
            let discriminant_call = self.inner.inner.lowerer.obtain_enum_discriminant(
                snapshot.clone(),
                self.inner.inner.ty,
                self.inner.inner.position,
            )?;
            let discriminant_snapshot = self.inner.inner.lowerer.construct_constant_snapshot(
                discriminant_type,
                discriminant_call,
                self.inner.inner.position,
            )?;
            expr! {
                ((old([memory_block_discriminant_bytes])) ==
                    (Snap<discriminant_type>::to_bytes([discriminant_snapshot])))
            }
        } else {
            true.into()
        };
        let expression = expr! {
            (discriminant == [discriminant_value.into()]) ==>
            (
                (
                    [discriminant_to_bytes] &&
                    ((old([memory_block_variant_bytes])) ==
                        (Snap<variant_type>::to_bytes([variant_snapshot])))
                ) ==>
                ([memory_block_bytes] == (Snap<ty>::to_bytes([snapshot])))
            )
        };
        Ok(expression)
    }

    pub(in super::super::super::super) fn add_variants_to_bytes_equalities_postcondition(
        &mut self,
        variant_to_bytes_equalities: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let ty = self.inner.inner.ty;
        let to_bytes = ty! { Bytes };
        let expression = expr! {
            forall(
                snapshot: {ty.to_snapshot(self.inner.inner.lowerer)?} ::
                [ { (Snap<ty>::to_bytes(snapshot)) } ]
                [ variant_to_bytes_equalities.into_iter().conjoin() ]
            )
        };
        self.add_postcondition(expression);
        Ok(())
    }
}
