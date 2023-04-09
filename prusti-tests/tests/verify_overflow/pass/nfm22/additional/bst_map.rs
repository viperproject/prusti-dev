#![feature(box_patterns)]
use prusti_contracts::*;
use std::cmp::{Ord, Ordering::{self, Equal, Less, Greater}, Eq};

fn main() { }

// TODO: Would be nice to get invariants working!
pub enum Tree<T: Ord, V: Eq> {
    Node(T, V, Box<Tree<T, V>>, Box<Tree<T, V>>),
    Empty,
}

#[extern_spec]
trait Ord {
    #[pure]
    // TODO: move `compare` spec here
    fn cmp(&self, other: &Self) -> Ordering;
}

// Issue 1: could not use `a.cmp(other)` directly within a `forall`
// as it would complain about `cmp` not being pure. May be related to issue #4?
#[pure]
#[trusted]
#[ensures(match (result, compare(b, a)) {
    (Equal, Equal) |
    (Less, Greater) |
    (Greater, Less) => true,
    _ => false,
})]
#[ensures(forall(|c: &T| match (result, compare(b, c), compare(a, c)) {
    (Equal, Equal, Equal) => true,
    (Equal, Less, Less) => true,
    (Equal, Greater, Greater) => true,
    (Less, Equal, Less) => true,
    (Less, Less, Less) => true,
    (Less, Greater, _) => true,
    (Greater, Equal, Greater) => true,
    (Greater, Less, _) => true,
    (Greater, Greater, Greater) => true,
    _ => false,
}))]
fn compare<T: Ord>(a: &T, b: &T) -> Ordering {
    a.cmp(b)
}

/*
#[extern_spec]
trait PartialEq {
    #[pure]
    fn eq(&self, other: &Self) -> bool;
}

#[pure]
#[trusted]
#[ensures(forall(|v: V| eq(&v, &v)))]
fn eq<V: Eq>(a: &V, b: &V) -> bool {
    a.eq(b)
}
*/

impl<T: Ord, V: Eq> Tree<T, V> {
    #[pure]
    pub fn contains(&self, find_key: &T) -> bool {
        if let Tree::Node(key, _, left, right) = self {
            match compare(find_key, key) {
                Equal => true,
                Less => left.contains(find_key),
                Greater => right.contains(find_key),
            }
        } else { false }
    }
    predicate! {
    pub fn bst_invariant(&self) -> bool {
        if let Tree::Node(key, _, left, right) = self {
            forall(|i: T| left.contains(&i) == (matches!(compare(&i, key), Less) && self.contains(&i))) &&
            forall(|i: T| right.contains(&i) == (matches!(compare(&i, key), Greater) && self.contains(&i))) &&
            left.bst_invariant() && right.bst_invariant()
        } else { true }
    }
    }


    #[requires(self.contains(find_key))]
    #[requires(self.bst_invariant())]
    // Pledge Option 1:
    // A little boring, would be more interesting if we could get the
    // last line to work (but that might require this additional `compare_at` fn)
    #[after_expiry(
        forall(|i: &T| old(self.contains(i)) == self.contains(i))
        && self.bst_invariant()
        // This pledge doesn't work :(
        //&& after_expiry(self.compare_at(old(find_key), before_expiry(result))
    )]
    pub fn get_mut(&mut self, find_key: &T) -> &mut V {
        // We require box here to get around a Prusti bug:
        if let Tree::Node(key, value, box left, box right) = self {
            match compare(find_key, key) {
                Equal => value,
                Less => left.get_mut(find_key),
                Greater => right.get_mut(find_key),
            }
        } else { panic!() }
    }

    /*
    #[pure]
    #[requires(self.contains(find_key))]
    pub fn compare_at(&self, find_key: &T, find_value: &V) -> bool {
        if let Tree::Node(key, value, box left, box right) = self {
            match compare(find_key, key) {
                Equal => eq(find_value, value),
                Less => left.compare_at(find_key, find_value),
                Greater => right.compare_at(find_key, find_value),
            }
        } else { panic!() }
    }
    */

    // Note: the invariant is not actually needed:
    #[requires(self.bst_invariant())]
    #[ensures(self.bst_invariant())]
    // Issue 5: `new_value` isn't automatically wrapped in `old(...)` (due to snapshot encoding imo)
    #[ensures(self.contains(&old(new_key)))]
    #[ensures(forall(|i: &T| !matches!(compare(old(&new_key), i), Equal) ==> old(self.contains(i)) == self.contains(i)))]
    //#[ensures(self.compare_at(&old(new_key), &old(new_value)))]
    pub fn insert(&mut self, new_key: T, new_value: V) {
        if let Tree::Node(key, value, left, right) = self {
            match compare(&new_key, key) {
                Equal => *value = new_value,
                Less => left.insert(new_key, new_value),
                Greater => right.insert(new_key, new_value),
            }
        } else {
            *self = Tree::Node(new_key, new_value, Box::new(Tree::Empty), Box::new(Tree::Empty))
        }
    }
}
