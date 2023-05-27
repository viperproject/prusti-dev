use super::{
    common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods},
    memory_block_range_split_join_common::MemoryBlockRangeSplitJoinMethodBuilder,
    memory_block_split_join_common::BuiltinMethodSplitJoinBuilderMethods,
};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer,
        predicates::PredicatesMemoryBlockInterface, snapshots::SnapshotValuesInterface,
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct MemoryBlockRangeSplitMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: MemoryBlockRangeSplitJoinMethodBuilder<'l, 'p, 'v, 'tcx>,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockRangeSplitMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        self.inner.inner()
    }
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodSplitJoinBuilderMethods<'l, 'p, 'v, 'tcx>
    for MemoryBlockRangeSplitMethodBuilder<'l, 'p, 'v, 'tcx>
{
}

impl<'l, 'p, 'v, 'tcx> MemoryBlockRangeSplitMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            inner: MemoryBlockRangeSplitJoinMethodBuilder::new(
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

    // pub(in super::super::super::super) fn add_permission_amount_positive_precondition(
    //     &mut self,
    // ) -> SpannedEncodingResult<()> {
    //     self.inner.add_permission_amount_positive_precondition()
    // }

    pub(in super::super::super::super) fn add_whole_memory_block_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let memory_block = self.inner.create_whole_block_acc()?;
        self.add_precondition(memory_block);
        Ok(())
    }

    pub(in super::super::super::super) fn add_memory_block_range_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let memory_block_range = self.inner.create_memory_block_range_acc()?;
        self.add_postcondition(memory_block_range);
        Ok(())
    }

    // FIXME: Code duplication.
    pub(in super::super::super::super) fn add_byte_values_preserved_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let element_size = self
            .inner
            .inner
            .lowerer
            .encode_type_size_expression2(self.inner.inner.ty, self.inner.inner.type_decl)?;
        let length = self.inner.length()?;
        let whole_size = self
            .inner
            .inner
            .lowerer
            .encode_type_size_expression_repetitions(
                self.inner.inner.ty,
                self.inner.inner.type_decl,
                length,
                self.inner.inner.position,
            )?;
        let size_type = self.inner.inner.lowerer.size_type_mid()?;
        var_decls! {
            index: Int,
            byte_index: Int
        }
        let address: vir_low::Expression = self.inner.address.clone().into();
        let element_address = self.inner.inner.lowerer.address_offset(
            element_size.clone(),
            address.clone(),
            index.clone().into(),
            self.inner.inner.position,
        )?;
        // let predicate =
        //     self.encode_memory_block_acc(element_address.clone(), size.clone(), position)?;
        let start_index = self.inner.inner.lowerer.obtain_constant_value(
            &size_type,
            self.inner.start_index.clone().into(),
            self.inner.inner.position,
        )?;
        let end_index = self.inner.inner.lowerer.obtain_constant_value(
            &size_type,
            self.inner.end_index.clone().into(),
            self.inner.inner.position,
        )?;
        let element_bytes = self
            .inner
            .inner
            .lowerer
            .encode_memory_block_bytes_expression(element_address, element_size.clone())?;
        let whole_bytes = self
            .inner
            .inner
            .lowerer
            .encode_memory_block_bytes_expression(address, whole_size)?;
        let read_element_byte = self.inner.inner.lowerer.encode_read_byte_expression_int(
            element_bytes,
            byte_index.clone().into(),
            self.inner.inner.position,
        )?;
        let block_size = self.inner.inner.lowerer.obtain_constant_value(
            &size_type,
            element_size.clone(),
            self.inner.inner.position,
        )?;
        let block_start_index = vir_low::Expression::multiply(block_size, index.clone().into());
        let whole_byte_index =
            vir_low::Expression::add(block_start_index, byte_index.clone().into());
        // let whole_byte_index = self.inner.inner.lowerer.create_domain_func_app(
        //     "Arithmetic",
        //     "mul_add",
        //     vec![block_size, index.clone().into(), byte_index.clone().into()],
        //     vir_low::Type::Int,
        //     self.inner.inner.position,
        // )?;
        let read_whole_byte = self.inner.inner.lowerer.encode_read_byte_expression_int(
            vir_low::Expression::labelled_old(None, whole_bytes, self.inner.inner.position),
            whole_byte_index,
            self.inner.inner.position,
        )?;
        let element_size_int = self.inner.inner.lowerer.obtain_constant_value(
            &size_type,
            element_size,
            self.inner.inner.position,
        )?;
        let body = expr!(
            ((([start_index] <= index) && (index < [end_index])) &&
            (([0.into()] <= byte_index) && (byte_index < [element_size_int]))) ==>
            ([read_element_byte.clone()] == [read_whole_byte])
        );
        let trigger = read_element_byte;
        let expression = vir_low::Expression::forall(
            vec![index, byte_index],
            vec![vir_low::Trigger::new(vec![trigger])],
            body,
        );
        self.add_postcondition(expression);
        Ok(())
    }
}
