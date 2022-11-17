use prusti_contracts::*;
use std::collections::HashSet;
use std::hash::Hash;

struct WrappedHashSet<T>{
    set: HashSet<T>
}

impl<T: Hash + Eq> WrappedHashSet<T>{
    #[trusted]
    #[ensures(result.is_empty())]
    fn new() -> Self {
        WrappedHashSet{
            set: HashSet::new()
        }
    }

    #[pure]
    #[trusted]
    #[ensures(result >= 0)]
    fn len(&self) -> usize {
        return self.set.len();
    }

    #[pure]
    #[trusted]
    #[ensures(result ==> self.len() > 0)]
    #[ensures(!result ==> self.len() == 0)]
    fn is_empty(&self) -> bool {
        self.set.is_empty()
    }

    #[trusted]
    #[ensures(self.is_empty())]
    fn clear(&mut self) {
        self.set.clear();
    }

    #[trusted]
    #[pure]
    fn contains(&self, elem: &T) -> bool {
        self.set.contains(elem)
    }

    #[trusted]
    #[ensures(result ==> !old(self).contains(&old(elem)))]
    #[ensures(!result ==> old(self).contains(&old(elem)))]
    #[ensures(self.contains(&old(elem)))]
    fn insert(&mut self, elem: T) -> bool {
        self.set.insert(elem)
    }
}

// Taken from Meirim, Filipe, Mário Pereira, and Carla Ferreira. 
// "CISE3: Verifying Weakly Consistent Applications with Why3." arXiv preprint arXiv:2010.06622 (2020).
struct RemoveWinsSet<T>{
    remove_wins_adds: WrappedHashSet<T>,
    remove_wins_removes: WrappedHashSet<T>
}

impl<T: Hash + Eq> RemoveWinsSet<T>{
    #[ensures(result.remove_wins_adds.is_empty() && result.remove_wins_removes.is_empty())]
    fn new() -> Self {
        RemoveWinsSet{
            remove_wins_adds: WrappedHashSet::new(),
            remove_wins_removes: WrappedHashSet::new()
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
