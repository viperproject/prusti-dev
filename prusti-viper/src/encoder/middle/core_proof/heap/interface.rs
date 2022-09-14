use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::{common::expression::QuantifierHelpers, low as vir_low};

const HEAP_DOMAIN_NAME: &str = "Heap$";
const HEAP_LOOKUP_FUNCTION_NAME: &str = "heap$lookup";
const HEAP_UPDATE_FUNCTION_NAME: &str = "heap$update";
const HEAP_CHUNK_TYPE_NAME: &str = "HeapChunk$";

pub(in super::super) trait Private {
    fn encode_heap_axioms(&mut self) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_heap_axioms(&mut self) -> SpannedEncodingResult<()> {
        if !self.heap_state.is_heap_encoded {
            self.heap_state.is_heap_encoded = true;

            let position = vir_low::Position::default();
            use vir_low::macros::*;
            let heap_type = self.heap_type()?;
            let heap_chunk_type = self.heap_chunk_type()?;
            var_decls!(
                heap: {heap_type.clone()},
                address: Address,
                chunk: {heap_chunk_type.clone()}
            );
            let update_call = self.create_domain_func_app(
                HEAP_DOMAIN_NAME,
                HEAP_UPDATE_FUNCTION_NAME,
                vec![
                    heap.clone().into(),
                    address.clone().into(),
                    chunk.clone().into(),
                ],
                heap_type,
                position,
            )?;
            {
                let lookup_call = self.create_domain_func_app(
                    HEAP_DOMAIN_NAME,
                    HEAP_LOOKUP_FUNCTION_NAME,
                    vec![update_call.clone(), address.clone().into()],
                    heap_chunk_type.clone(),
                    position,
                )?;

                // forall heap: Heap$, addr: Address, chunk: HeapChunk$ ::
                //      { heap$lookup(heap$update(heap, addr, chunk), addr) }
                //      heap$lookup(heap$update(heap, addr, chunk), addr) == chunk
                let axiom_update_value = vir_low::DomainAxiomDecl {
                    comment: None,
                    name: "heap$update_value$axiom".to_string(),
                    body: QuantifierHelpers::forall(
                        vec![heap.clone(), address.clone(), chunk.clone()],
                        vec![vir_low::Trigger::new(vec![lookup_call.clone()])],
                        expr! {
                            [lookup_call] == chunk
                        },
                    ),
                };
                self.declare_axiom(HEAP_DOMAIN_NAME, axiom_update_value)?;
            }
            {
                var_decls!(address2: Address);
                let lookup_call_original = self.create_domain_func_app(
                    HEAP_DOMAIN_NAME,
                    HEAP_LOOKUP_FUNCTION_NAME,
                    vec![heap.clone().into(), address2.clone().into()],
                    heap_chunk_type.clone(),
                    position,
                )?;
                let lookup_call_updated = self.create_domain_func_app(
                    HEAP_DOMAIN_NAME,
                    HEAP_LOOKUP_FUNCTION_NAME,
                    vec![update_call, address2.clone().into()],
                    heap_chunk_type,
                    position,
                )?;
                // forall heap: Heap$, addr1: Address, addr2: Address, chunk: HeapChunk$ ::
                //      { heap$lookup(heap$update(heap, addr1, chunk), addr2) }
                //      addr1 != addr2 ==>
                //      heap$lookup(heap$update(heap, addr1, chunk), addr2) == heap$lookup(heap, addr2)
                let axiom_preserve_value = vir_low::DomainAxiomDecl {
                    name: "heap$update_preserve_value$axiom".to_string(),
                    comment: None,
                    body: QuantifierHelpers::forall(
                        vec![heap, address.clone(), address2.clone(), chunk],
                        vec![vir_low::Trigger::new(vec![lookup_call_updated.clone()])],
                        expr! {
                            (address != address2) ==>
                            ([lookup_call_updated] == [lookup_call_original])
                        },
                    ),
                };
                self.declare_axiom(HEAP_DOMAIN_NAME, axiom_preserve_value)?;
            }
        }
        Ok(())
    }
}

pub(in super::super) trait HeapInterface {
    fn heap_lookup(
        &mut self,
        heap: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn heap_update(
        &mut self,
        heap: vir_low::Expression,
        address: vir_low::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn heap_chunk_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn heap_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
}

impl<'p, 'v: 'p, 'tcx: 'v> HeapInterface for Lowerer<'p, 'v, 'tcx> {
    fn heap_lookup(
        &mut self,
        _heap: vir_low::Expression,
        _address: vir_low::Expression,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!("outdated-code");
        // self.encode_heap_axioms()?;
        // let return_type = self.heap_chunk_type()?;
        // self.create_domain_func_app(
        //     HEAP_DOMAIN_NAME,
        //     HEAP_LOOKUP_FUNCTION_NAME,
        //     vec![heap, address],
        //     return_type,
        //     position,
        // )
    }
    fn heap_update(
        &mut self,
        heap: vir_low::Expression,
        address: vir_low::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_heap_axioms()?;
        let return_type = self.heap_type()?;
        self.create_domain_func_app(
            HEAP_DOMAIN_NAME,
            HEAP_UPDATE_FUNCTION_NAME,
            vec![heap, address, value],
            return_type,
            position,
        )
    }
    fn heap_chunk_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(HEAP_CHUNK_TYPE_NAME)
    }
    fn heap_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type(HEAP_DOMAIN_NAME)
    }
}
