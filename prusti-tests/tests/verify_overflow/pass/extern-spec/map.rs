use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[pure]
    pub fn is_some(&self) -> bool;
}

#[extern_spec]
impl<K, V, S: std::hash::BuildHasher> std::collections::HashMap<K, V, S> {
    #[pure]
    #[ensures(result.is_some() == self.contains_key(k))]
    pub fn get<'a, Q: ?Sized>(&'a self, k: &Q) -> Option<&'a V>
    where
        K: core::borrow::Borrow<Q> + std::cmp::Eq + std::hash::Hash,
        Q: core::hash::Hash + Eq;

    #[pure]
    fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: core::borrow::Borrow<Q> + std::cmp::Eq + std::hash::Hash,
        Q: core::hash::Hash + Eq;
}

#[requires(m.contains_key(&key))]
fn go(key: u32, m: &std::collections::HashMap<u32, bool>) {
    let result = m.get(&key);
    assert!(result.is_some())
}

fn main(){
}
