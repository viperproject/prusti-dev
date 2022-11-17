use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::{
            DomainsLowererInterface, FunctionsLowererInterface, Lowerer, PredicatesLowererInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::low as vir_low;

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
    fn encode_memory_block_predicate(&mut self) -> SpannedEncodingResult<()>;
    fn encode_memory_block_stack_drop_acc(
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
    fn encode_memory_block_predicate(&mut self) -> SpannedEncodingResult<()> {
        self.encode_generic_memory_block_predicate("MemoryBlock")
    }
    fn encode_memory_block_stack_drop_acc(
        &mut self,
        place: vir_low::Expression,
        size: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_generic_memory_block_acc("MemoryBlockStackDrop", place, size, position)
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
