use prusti_contracts::*;

#[derive(Clone)]
pub enum Item<V> {
    Empty,
    Entry{key: usize, value: V},
    Tombstone{key: usize}
}

pub use Item::{Empty, Entry, Tombstone};

impl<V> Item<V> {
    #[pure]
    pub fn is_empty(&self) -> bool {
        matches!(self, Empty)
    }
    #[pure]
    pub fn is_entry(&self) -> bool {
        matches!(self, Entry{..})
    }
    #[pure]
    pub fn is_tombstone(&self) -> bool {
        matches!(self, Tombstone{..})
    }
}

#[derive(Copy, Clone)]
pub struct Slot{
    ghost_slot: usize,
}

impl Slot {
    #[pure]
    pub fn new(ghost_slot: usize) -> Self {
        Self { ghost_slot }
    }
}

#[pure]
pub fn hash64(k: usize) -> usize {
    k // TODO
}

#[requires(len > 0)]
#[requires(slot < len)]
pub fn slot_succ(len: usize, slot: usize) -> usize {
    if slot == len - 1 {
        0
    } else {
        slot + 1
    }
}