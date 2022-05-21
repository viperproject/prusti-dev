use crate::base::*;
use prusti_contracts::*;

use super::linear_mutable_map_base::*;

pub struct FixedSizeLinearHashMap<V> {
    storage: Vector<Item<V>>,
    count: u64,
}

impl<V: Clone> FixedSizeLinearHashMap<V> {
    #[pure]
    fn inv(&self) -> bool {
        128 <= self.storage.len() && self.count < self.storage.len()
    }

    #[requires(128 <= size)]
    #[ensures(result.inv())]
    pub fn with_size(size: u64) -> Self {
        let storage = Vector::init(Empty, size);
        Self { storage, count: 0 }
    }

    #[requires(128 <= storage.len())]
    #[ensures(result.inv())]
    pub fn from_storage(storage: Vector<Item<V>>) -> Self {
        let mut count = 0;
        let mut i = 0;
        while i < storage.len() {
            if storage.index(i).is_entry() {
                count += 1;
            }
            i += 1;
        }
        Self { storage, count }
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn slot_for_key(&self, key: u64) -> u64 {
        let h = hash64(key);
        let len = self.storage.len();
        h % len
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn get_empty_witness(&self, i: u64) -> u64 {
        let entry = self.storage.index(i);
        match entry {
            Empty => i,
            _ => self.get_empty_witness(i + 1),
        }
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn probe(&self, key: u64) -> u64 {
        let mut slot_idx = self.slot_for_key(key);
        let start_slot_idx = slot_idx;
        let mut done = false;

        while !done {
            body_invariant!(self.inv());
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

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn insert(&mut self, key: u64, value: V) -> Opt<V> {
        let mut slot_idx = self.probe(key);
        let slot = self.storage.index_mut(slot_idx);
        let original = replace(slot, Entry { key, value });
        match original {
            Entry { key: _, value } => Opt::Some(value),
            _ => {
                self.count += 1;
                Opt::None
            }
        }
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn update_slot(&mut self, slot_idx: u64, value: V) {
        let slot = self.storage.index_mut(slot_idx);
        match slot {
            Entry { key: _, value: val } => {
                *val = value;
            }
            _ => (),
        }
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn remove(&mut self, key: u64) -> Opt<V> {
        let slot_idx = self.probe(key);
        let slot = self.storage.index_mut(slot_idx);
        if slot.is_entry() {
            let old = replace(slot, Tombstone { key });
            match old {
                Entry { key: _, value } => {
                    self.count -= 1;
                    Opt::Some(value)
                }
                _ => unreachable!(),
            }
        } else {
            Opt::None
        }
    }

    #[requires(self.inv())]
    #[ensures(self.inv())]
    pub fn get(&self, key: u64) -> Opt<V> {
        let slot_idx = self.probe(key);
        let slot = self.storage.index(slot_idx);
        match slot {
            Entry { key: _, value: val } => Opt::Some(val.clone()),
            _ => Opt::None,
        }
    }
}

pub struct LinearHashMap<V> {
    inner: FixedSizeLinearHashMap<V>,
    count: u64,
}

impl<V: Clone> LinearHashMap<V> {
    #[requires(128 <= size)]
    pub fn with_size(size: u64) -> Self {
        Self {
            inner: FixedSizeLinearHashMap::with_size(size),
            count: 0,
        }
    }

    pub fn realloc(&mut self) {
        let new_size = (128 + self.count) * 4;
        let mut new_inner = FixedSizeLinearHashMap::with_size(new_size);

        let mut i = 0;
        while i < self.inner.storage.len() {
            let item = self.inner.storage.index(i).clone();
            if let Entry { key, value } = item {
                new_inner.insert(key, value);
            }
            i += 1;
        }

        self.inner = new_inner;
    }

    pub fn insert(&mut self, key: u64, value: V) -> Opt<V> {
        if self.inner.storage.len() / 2 < self.inner.count {
            self.realloc();
        }
        let replaced = self.inner.insert(key, value);
        if replaced.is_none() {
            self.count += 1;
        }
        replaced
    }

    pub fn remove(&mut self, key: u64) -> Opt<V> {
        let removed = self.inner.remove(key);
        if removed.is_some() {
            self.count -= 1;
        }
        removed
    }

    pub fn get(&self, key: u64) -> Opt<V> {
        self.inner.get(key)
    }
}
