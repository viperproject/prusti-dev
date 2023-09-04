use prusti_contracts::*;

#[extern_spec]
impl<K, V, S> std::collections::hash_map::HashMap<K, V, S>
where
    K: Eq + ::core::hash::Hash,
    S: ::std::hash::BuildHasher,
{
    #[pure]
    #[ensures(result.is_some() == self.contains_key(k))]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
    where
        K: core::borrow::Borrow<Q> + std::cmp::Eq + std::hash::Hash,
        Q: core::hash::Hash + Eq;

    #[pure]
    fn contains_key<Q: ?Sized>(&self, k: &Q) -> bool
    where
        K: core::borrow::Borrow<Q> + Eq + std::hash::Hash,
        Q: core::hash::Hash + Eq;
}
