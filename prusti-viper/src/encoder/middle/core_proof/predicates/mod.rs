mod memory_block;
mod owned;
mod state;

pub(super) use self::{
    memory_block::PredicatesMemoryBlockInterface, owned::PredicatesOwnedInterface,
    state::PredicatesState,
};
