use super::{
    aliasing::PredicatesAliasingState, memory_block::PredicatesMemoryBlockState,
    owned::PredicatesOwnedState, restoration::RestorationState,
};

#[derive(Default)]
pub(in super::super) struct PredicatesState {
    pub(super) owned: PredicatesOwnedState,
    pub(super) memory_block: PredicatesMemoryBlockState,
    pub(super) restoration: RestorationState,
    pub(super) aliasing: PredicatesAliasingState,
}
