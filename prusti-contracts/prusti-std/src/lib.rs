use prusti_contracts::*;

#[extern_spec]
impl<K, V, S> ::std::collections::hash_map::HashMap<K, V, S>
where
    K: Eq + ::core::hash::Hash,
    S: ::std::hash::BuildHasher,
{
    #[pure]
    pub fn contains_key<Q>(&self, k: &Q) -> bool where K: ::core::borrow::Borrow<Q>, Q: ::core::hash::Hash + Eq;
}
