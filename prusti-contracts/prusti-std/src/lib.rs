use prusti_contracts::*;

#[extern_spec]
impl<K, V, S> ::std::collections::hash_map::HashMap<K, V, S>
where
    K: ::std::cmp::Eq + ::std::hash::Hash,
    S: ::std::hash::BuildHasher,
{
    #[pure]
    pub fn contains_key<Q>(&self, k: &K) -> bool;
}
