use prusti_contracts::*;
use std::collections::HashMap;
use std::hash::{Hash, BuildHasher};

#[extern_spec]
impl<K, V, S> HashMap<K, V, S> {
    #[pure]
    fn len(&self) -> usize;
}

#[extern_spec]
impl<K, V, S> HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    #[ensures(snapshot_equality(result, None) ==> self.len() == old(self.len()) + 1)]
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

fn test(mut x: HashMap<u64, u64>) {
    let orig_len = x.len();
    if let None = x.insert(234, 345) {
        assert!(x.len() == orig_len + 1);
    }
}

#[trusted]
fn main() {}
