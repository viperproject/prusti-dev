use prusti_contracts::*;
use crate::base::*;

use super::linear_mutable_map_base::*;

pub struct FixedSizeLinearHashMap<V> {
    storage: Vector<Item<V>>,
    count: usize,
}

impl<V: Clone> FixedSizeLinearHashMap<V> {
    #[pure]
    fn inv(&self) -> bool {
        true // TODO
    }

    pub fn with_size(size: usize) -> Self {
        let storage = Vector::init(Empty, size);
        Self {
            storage,
            count: 0
        }
    }

    pub fn from_storage(storage: Vector<Item<V>>, count: usize) -> Self {
        Self {
            storage,
            count
        }
    }

    pub fn slot_for_key(&self, key: usize) -> usize {
        let h = hash64(key);
        let len = self.storage.len();
        h % len
    }

    pub fn get_empty_witness(&self, i: usize) -> usize {
        match self.storage.index(i) {
            Empty => i,
            _ => self.get_empty_witness(i+1)
        }
    }

    pub fn probe(&self, key: usize) -> usize {
        let mut slot_idx = self.slot_for_key(key);
        let start_slot_idx = slot_idx;
        let mut skips = 0;

        loop {
            let slot = &self.storage.index(slot_idx);
            match slot {
                Empty => return slot_idx,
                Tombstone{key: k} if key == *k => return slot_idx,
                Entry{key: k, ..} if key == *k => return slot_idx,
                _ => ()
            };
            slot_idx = slot_succ(self.storage.len(), slot_idx);
            skips += 1;
        }
    }

    pub fn insert(&mut self, key: usize, value: V) -> Opt<V> {
        todo!()
    }
}