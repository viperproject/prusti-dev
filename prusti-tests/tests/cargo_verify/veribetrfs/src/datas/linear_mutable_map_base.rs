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
#[trusted] // since no flags right now
pub fn hash64(k: usize) -> usize {
    let k0 = !k + k << 21;
    let k1 = k0 ^ (k0 >> 24);
    let k2 = k1 + k1 << 3 + k1 << 8;
    let k3 = k2 ^ k2 >> 14;
    let k4 = k3 + k3 << 2 + k3 << 4;
    let k5 = k4 ^ (k4 >> 28);
    let k6 = k5 + k5 << 31;
    k6
}

#[requires(len > 0)]
pub fn slot_succ(len: usize, slot: usize) -> usize {
    if slot >= len - 1 {
        0
    } else {
        slot + 1
    }
}