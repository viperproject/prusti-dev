use prusti_contracts::*;
use std::collections::HashSet;
use std::hash::{Hash, BuildHasher};

#[extern_spec]
impl<T> HashSet<T> {
    #[ensures(result.is_empty())]
    fn new() -> Self;
}

#[extern_spec]
impl<T, S: BuildHasher> HashSet<T, S> {
    #[pure]
    #[ensures(result >= 0)]
    fn len(&self) -> usize;

    #[pure]
    #[ensures(result ==> self.len() > 0)]
    #[ensures(!result ==> self.len() == 0)]
    fn is_empty(&self) -> bool;

    #[ensures(self.is_empty())]
    fn clear(&mut self);
}

#[extern_spec]
impl<T: Hash + Eq, S: BuildHasher> HashSet<T, S> {
    #[pure]
    fn contains<Q: Hash + Eq>(&self, elem: &Q) -> bool
        where T: std::borrow::Borrow<Q>;

    #[ensures(result ==> !old(self).contains(&old(elem)))]
    #[ensures(!result ==> old(self).contains(&old(elem)))]
    #[ensures(self.contains(&old(elem)))]
    fn insert(&mut self, elem: T) -> bool;
}

// Taken from Meirim, Filipe, Mário Pereira, and Carla Ferreira. 
// "CISE3: Verifying Weakly Consistent Applications with Why3." arXiv preprint arXiv:2010.06622 (2020).
struct RemoveWinsSet<T>{
    remove_wins_adds: HashSet<T>,
    remove_wins_removes: HashSet<T>
}

impl<T: Hash + Eq> RemoveWinsSet<T>{
    #[ensures(result.remove_wins_adds.is_empty() && result.remove_wins_removes.is_empty())]
    fn new() -> Self {
        RemoveWinsSet{
            remove_wins_adds: HashSet::new(),
            remove_wins_removes: HashSet::new()
        }
    }

    #[ensures(self.remove_wins_adds.is_empty() && self.remove_wins_removes.is_empty())]
    fn empty_set(&mut self) {
        self.remove_wins_adds.clear();
        self.remove_wins_removes.clear();
    }

    #[pure]
    #[ensures(result ==> self.remove_wins_adds.contains(elem) && !self.remove_wins_removes.contains(elem))]
    #[ensures(!result ==> !self.remove_wins_adds.contains(elem) || self.remove_wins_removes.contains(elem))]
    fn in_set(&self, elem: &T) -> bool {
        self.remove_wins_adds.contains(elem) && !self.remove_wins_removes.contains(elem)
    }

    #[ensures(self.remove_wins_adds.contains(&elem))]
    fn add_elem(&mut self, elem: T) {
        self.remove_wins_adds.insert(elem);
    }

    #[ensures(self.remove_wins_removes.contains(&elem))]
    fn remove_elem(&mut self, elem: T) {
        self.remove_wins_removes.insert(elem);
    }
}

#[trusted]
fn main() {}
