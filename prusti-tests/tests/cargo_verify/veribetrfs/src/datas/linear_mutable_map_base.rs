use prusti_contracts::*;

#[derive(Clone)]
pub enum Item<V> {
    Empty,
    Entry { key: u64, value: V },
    Tombstone { key: u64 },
}

pub use Item::{Empty, Entry, Tombstone};

impl<V> Item<V> {
    #[pure]
    pub fn is_empty(&self) -> bool {
        matches!(self, Empty)
    }
    #[pure]
    pub fn is_entry(&self) -> bool {
        matches!(self, Entry { .. })
    }
    #[pure]
    pub fn is_tombstone(&self) -> bool {
        matches!(self, Tombstone { .. })
    }
}

#[derive(Copy, Clone)]
pub struct Slot {
    ghost_slot: u64,
}

impl Slot {
    #[pure]
    pub fn new(ghost_slot: u64) -> Self {
        Self { ghost_slot }
    }
}

#[pure]
#[trusted]
fn add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

#[pure]
pub fn hash64(k: u64) -> u64 {
    let k0 = add(!k, k << 21);
    let k1 = k0 ^ (k0 >> 24);
    let k2 = add(k1, add(k1 << 3, k1 << 8));
    let k3 = k2 ^ (k2 >> 14);
    let k4 = add(k3, add(k3 << 2, k3 << 4));
    let k5 = k4 ^ (k4 >> 28);
    let k6 = add(k5, k5 << 31);
    k6
}

#[requires(len > 0)]
#[requires(slot < len)]
pub fn slot_succ(len: u64, slot: u64) -> u64 {
    if slot == len - 1 {
        0
    } else {
        slot + 1
    }
}
