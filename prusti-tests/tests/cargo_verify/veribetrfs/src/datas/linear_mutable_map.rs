use crate::base::*;
use prusti_contracts::*;

use super::linear_mutable_map_base::*;

pub struct FixedSizeLinearHashMap<V> {
    storage: Vector<Item<V>>,
    count: usize,
}

impl<V: Clone> FixedSizeLinearHashMap<V> {
    #[pure]
    fn inv(&self) -> bool {
        128 <= self.storage.len() && self.count < self.storage.len()
    }

    pub fn with_size(size: usize) -> Self {
        let storage = Vector::init(Empty, size);
        Self { storage, count: 0 }
    }

    pub fn from_storage(storage: Vector<Item<V>>, count: usize) -> Self {
        Self { storage, count }
    }

    #[requires(self.inv())]
    pub fn slot_for_key(&self, key: usize) -> usize {
        let h = hash64(key);
        let len = self.storage.len();
        h % len
    }

    #[requires(self.inv())]
    #[requires(i < self.storage.len())]
    pub fn get_empty_witness(&self, i: usize) -> usize {
        let entry = self.storage.index(i);
        match entry {
            Empty => i,
            _ => self.get_empty_witness(i + 1),
        }
    }

    #[requires(self.inv())]
    pub fn probe(&self, key: usize) -> usize {
        let mut slot_idx = self.slot_for_key(key);
        let start_slot_idx = slot_idx;
        let mut done = false;

        while !done {
            let k = key;
            match self.storage.index(slot_idx) {
                Empty => done = true,
                Tombstone { key } => {
                    if *key == k {
                        break;
                    }
                }
                Entry { key, .. } => {
                    if *key == k {
                        break;
                    }
                }
                _ => (),
            };
            slot_idx = slot_succ(self.storage.len(), slot_idx);
        }

        slot_idx
    }

    pub fn insert(&mut self, key: usize, value: V) -> Opt<V> {
        todo!()
    }
}
