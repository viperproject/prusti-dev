use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::{
            DomainsLowererInterface, FunctionsLowererInterface, Lowerer, PredicatesLowererInterface,
        },
        snapshots::SnapshotValuesInterface,
        type_layouts::TypeLayoutsInterface,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{common::expression::QuantifierHelpers, low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct PredicatesMemoryBlockState {
    encoded_predicates: FxHashSet<String>,
    is_memory_block_bytes_encoded: bool,
}

trait Private {
    fn encode_generic_memory_block_predicate(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<()>;
    fn encode_generic_memory_block_acc(
        &mut self,
        predicate_name: &str,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_generic_memory_block_predicate(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<()> {
        if !self
            .predicates_encoding_state
            .memory_block
            .encoded_predicates
            .contains(predicate_name)
        {
            self.predicates_encoding_state
                .memory_block
                .encoded_predicates
                .insert(predicate_name.to_string());
            let predicate = vir_low::PredicateDecl::new(
                predicate_name,
                vec![
                    vir_low::VariableDecl::new("address", self.address_type()?),
                    vir_low::VariableDecl::new("size", self.size_type()?),
                ],
                None,
            );
            self.declare_predicate(predicate)?;
        }
        Ok(())
    }
    fn encode_generic_memory_block_acc(
        &mut self,
        predicate_name: &str,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_generic_memory_block_predicate(predicate_name)?;
        let expression = vir_low::Expression::predicate_access_predicate(
            predicate_name.to_string(),
            vec![place, size],
            vir_low::Expression::full_permission(),
            position,
        );
        Ok(expression)
    }
}

pub(in super::super::super) trait PredicatesMemoryBlockInterface {
    fn bytes_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn byte_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn encode_read_byte_expression(
        &mut self,
        bytes: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_memory_block_predicate(&mut self) -> SpannedEncodingResult<()>;
    fn encode_memory_block_stack_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_memory_block_range_acc(
        &mut self,
        address: vir_low::Expression,
        size: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_memory_block_stack_drop_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_memory_block_heap_drop_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_memory_block_bytes_function_name(&mut self) -> SpannedEncodingResult<String>;
    fn encode_memory_block_bytes_expression(
        &mut self,
        address: vir_low::Expression,
        size: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PredicatesMemoryBlockInterface for Lowerer<'p, 'v, 'tcx> {
    fn bytes_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("Bytes")
    }
    fn byte_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("Byte")
    }
    fn encode_read_byte_expression(
        &mut self,
        bytes: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let byte_type = self.byte_type()?;
        self.create_domain_func_app(
            "Byte",
            "Byte$read_byte",
            vec![bytes, index],
            byte_type,
            position,
        )
    }
    fn encode_memory_block_predicate(&mut self) -> SpannedEncodingResult<()> {
        self.encode_generic_memory_block_predicate("MemoryBlock")
    }
    fn encode_memory_block_stack_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_generic_memory_block_acc("MemoryBlock", place, size, position)
    }
    fn encode_memory_block_range_acc(
        &mut self,
        address: vir_low::Expression,
        size: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let size_type = self.size_type_mid()?;
        var_decls! {
            index: Int
        }
        let element_address =
            self.address_offset(size.clone(), address, index.clone().into(), position)?;
        let predicate =
            self.encode_memory_block_stack_acc(element_address.clone(), size.clone(), position)?;
        let start_index = self.obtain_constant_value(&size_type, start_index, position)?;
        let end_index = self.obtain_constant_value(&size_type, end_index, position)?;
        let body = expr!(
            (([start_index] <= index) && (index < [end_index])) ==> [predicate]
        );
        let expression = vir_low::Expression::forall(
            vec![index],
            vec![vir_low::Trigger::new(vec![element_address])],
            body,
        );
        Ok(expression)
    }
    fn encode_memory_block_stack_drop_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_generic_memory_block_acc("MemoryBlockStackDrop", place, size, position)
    }
    fn encode_memory_block_heap_drop_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_generic_memory_block_acc("MemoryBlockHeapDrop", place, size, position)
    }
    fn encode_memory_block_bytes_function_name(&mut self) -> SpannedEncodingResult<String> {
        Ok("MemoryBlock$bytes".to_string())
    }
    fn encode_memory_block_bytes_expression(
        &mut self,
        address: vir_low::Expression,
        size: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if !self
            .predicates_encoding_state
            .memory_block
            .is_memory_block_bytes_encoded
        {
            use vir_low::macros::*;
            let mut function = function! { MemoryBlockBytes =>
                bytes(
                    address: Address,
                    size: {ty! {{ self.size_type()? }}}
                ): Bytes
                    requires (acc(
                        MemoryBlock(address, size),
                        [vir_low::Expression::wildcard_permission()]
                    ));
            };
            function.name = "MemoryBlock$bytes".to_string();
            self.declare_function(function)?;
            self.predicates_encoding_state
                .memory_block
                .is_memory_block_bytes_encoded = true;
        }
        let expression = vir_low::Expression::function_call(
            self.encode_memory_block_bytes_function_name()?,
            vec![address, size],
            self.bytes_type()?,
        );
        Ok(expression)
    }
}
