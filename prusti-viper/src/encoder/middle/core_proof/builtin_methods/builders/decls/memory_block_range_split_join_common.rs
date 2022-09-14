use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer,
        predicates::PredicatesMemoryBlockInterface, snapshots::SnapshotValuesInterface,
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super) struct MemoryBlockRangeSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(super) inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    pub(super) address: vir_low::VariableDecl,
    pub(super) start_index: vir_low::VariableDecl,
    pub(super) end_index: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockRangeSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

pub(in super::super) trait BuiltinMethodSplitJoinBuilderMethods<'l, 'p, 'v, 'tcx>:
    Sized + BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
where
    'p: 'l,
    'v: 'p,
    'tcx: 'v,
{
}

impl<'l, 'p, 'v, 'tcx> MemoryBlockRangeSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let address = vir_low::VariableDecl::new("address", lowerer.address_type()?);
        let size_type = lowerer.size_type()?;
        let start_index = vir_low::VariableDecl::new("start_index", size_type.clone());
        let end_index = vir_low::VariableDecl::new("end_index", size_type);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            address,
            start_index,
            end_index,
        })
    }

    pub(in super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    // pub(in super::super) fn address(&self) -> vir_low::Expression {
    //     self.address.clone().into()
    // }

    pub(in super::super) fn create_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.address.clone());
        self.inner.parameters.push(self.start_index.clone());
        self.inner.parameters.push(self.end_index.clone());
        Ok(())
    }

    pub(in super::super) fn length(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        let size_type = self.inner.lowerer.size_type_mid()?;
        self.inner.lowerer.construct_binary_op_snapshot(
            vir_mid::BinaryOpKind::Sub,
            &size_type,
            &size_type,
            self.end_index.clone().into(),
            self.start_index.clone().into(),
            self.inner.position,
        )
    }

    // pub(in super::super) fn add_permission_amount_positive_precondition(
    //     &mut self,
    // ) -> SpannedEncodingResult<()> {
    //     let expression = self
    //         .inner
    //         .create_permission_amount_positive(&self.permission_amount)?;
    //     self.add_precondition(expression);
    //     Ok(())
    // }

    pub(in super::super) fn create_whole_block_acc(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // self.create_memory_block(self.address.clone().into())
        use vir_low::macros::*;
        let length = self.length()?;
        let inner = self.inner();
        let size_of = inner.lowerer.encode_type_size_expression_repetitions(
            inner.ty,
            inner.type_decl,
            length,
            inner.position,
        )?;
        let address = &self.address;
        Ok(expr! {
            acc(MemoryBlock(address, [size_of]))
        })
    }

    pub(in super::super) fn create_memory_block_range_acc(
        &mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // self.create_memory_block(self.address.clone().into())
        let size_of = self
            .inner
            .lowerer
            .encode_type_size_expression2(self.inner.ty, self.inner.type_decl)?;
        self.inner.lowerer.encode_memory_block_range_acc(
            self.address.clone().into(),
            size_of,
            self.start_index.clone().into(),
            self.end_index.clone().into(),
            self.inner.position,
        )
    }

    // pub(in super::super) fn padding_size(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
    //     self.inner
    //         .lowerer
    //         .encode_type_padding_size_expression(self.inner.ty)
    // }

    // pub(in super::super) fn create_padding_memory_block_acc(
    //     &mut self,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let address = self.address.clone().into();
    //     let padding_size = self.padding_size()?;
    //     let permission_amount = self.permission_amount.clone().into();
    //     let expression = expr! {
    //         acc(MemoryBlock([address], [padding_size]), [permission_amount])
    //     };
    //     Ok(expression)
    // }

    // pub(in super::super) fn create_field_memory_block_acc(
    //     &mut self,
    //     field: &vir_mid::FieldDecl,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let field_address = self.inner.lowerer.encode_field_address(
    //         self.inner.ty,
    //         field,
    //         self.address.clone().into(),
    //         self.inner.position,
    //     )?;
    //     let field_size_of = self
    //         .inner
    //         .lowerer
    //         .encode_type_size_expression2(&field.ty, &field.ty)?;
    //     let permission_amount = self.permission_amount.clone().into();
    //     let field_block = expr! {
    //         acc(MemoryBlock([field_address], [field_size_of]), [permission_amount])
    //     };
    //     Ok(field_block)
    // }

    // pub(in super::super) fn create_discriminant_acc(
    //     &mut self,
    //     decl: &vir_mid::type_decl::Enum,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let discriminant_size_of = self
    //         .inner
    //         .lowerer
    //         .encode_type_size_expression2(&decl.discriminant_type, &decl.discriminant_type)?;
    //     let discriminant_field = decl.discriminant_field();
    //     let discriminant_address = self.inner.lowerer.encode_field_address(
    //         self.inner.ty,
    //         &discriminant_field,
    //         self.address.clone().into(),
    //         self.inner.position,
    //     )?;
    //     let discriminant_block = expr! {
    //         acc(MemoryBlock([discriminant_address], [discriminant_size_of]))
    //     };
    //     Ok(discriminant_block)
    // }

    // pub(in super::super) fn create_variant_memory_block_acc(
    //     &mut self,
    //     discriminant_value: vir_mid::DiscriminantValue,
    //     variant: &vir_mid::type_decl::Struct,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let variant_index = variant.name.clone().into();
    //     let variant_address = self.inner.lowerer.encode_enum_variant_address(
    //         self.inner.ty,
    //         &variant_index,
    //         self.address.clone().into(),
    //         Default::default(),
    //     )?;
    //     let variant_type = self.inner.ty.clone().variant(variant_index);
    //     let variant_size_of = self
    //         .inner
    //         .lowerer
    //         // .encode_type_size_expression(&variant_type)?;
    //         // FIXME: This is probably wrong: test enums containing arrays.
    //         .encode_type_size_expression2(&variant_type, &variant_type)?;
    //     let discriminant = self.discriminant.as_ref().unwrap().clone().into();
    //     let expression = expr! {
    //         ([discriminant] == [discriminant_value.into()]) ==>
    //         (acc(MemoryBlock([variant_address], [variant_size_of])))
    //     };
    //     Ok(expression)
    // }

    // pub(in super::super) fn create_field_to_bytes_equality(
    //     &mut self,
    //     field: &vir_mid::FieldDecl,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     use vir_low::macros::*;
    //     let address = self.address();
    //     let inner = self.inner();
    //     inner.lowerer.encode_snapshot_to_bytes_function(inner.ty)?;
    //     let field_address =
    //         inner
    //             .lowerer
    //             .encode_field_address(inner.ty, field, address, inner.position)?;
    //     let field_size_of = inner
    //         .lowerer
    //         .encode_type_size_expression2(&field.ty, &field.ty)?;
    //     let memory_block_field_bytes = inner
    //         .lowerer
    //         .encode_memory_block_bytes_expression(field_address, field_size_of)?;
    //     let snapshot = var! { snapshot: {inner.ty.to_snapshot(inner.lowerer)?} }.into();
    //     let field_snapshot = inner.lowerer.obtain_struct_field_snapshot(
    //         inner.ty,
    //         field,
    //         snapshot,
    //         inner.position,
    //     )?;
    //     let to_bytes = ty! { Bytes };
    //     Ok(expr! {
    //         (([memory_block_field_bytes])) == (Snap<(&field.ty)>::to_bytes([field_snapshot]))
    //     })
    // }
}
