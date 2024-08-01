#[derive(Default)]
pub(in super::super) struct AddressState {
    pub(super) are_address_axioms_encoded: bool,
    // pub(super) is_address_range_contains_axiom_encoded: bool,
    pub(super) fresh_allocation_counter: usize,
}
