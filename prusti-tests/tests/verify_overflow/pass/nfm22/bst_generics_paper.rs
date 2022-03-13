// Version of the example that doesn't yet work
// but will be included in the paper. We should
// make this work by the deadline
use prusti_contracts::*;
use std::cmp::{Ord, Ordering::{self, Equal, Less, Greater}};

fn main() {
    let v = 0;
    let t = Tree::Node(v, Box::new(Tree::Empty), Box::new(Tree::Empty));
    assert!(t.contains(&v));
}

#[invariant(self.bst_invariant())]
pub enum Tree<T: Ord> {
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
    Empty,
}

#[extern_spec]
trait Ord {
    #[pure]
    #[ensures(match (result, Self::cmp(other, self)) {
        (Equal, Equal) |
        (Less, Greater) |
        (Greater, Less) => true,
        _ => false,
    })]
    #[ensures(forall(|x: &Self| match (result, Self::cmp(other, x), Self::cmp(self, x)) {
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
    fn cmp(&self, other: &Self) -> Ordering;
}

impl<T: Ord> Tree<T> {
    #[pure]
    pub fn contains(&self, find_value: &T) -> bool {
        if let Tree::Node(value, left, right) = self {
            match find_value.cmp(value) {
                Equal => true,
                Less => left.contains(find_value),
                Greater => right.contains(find_value),
            }
        } else { false }
    }

    predicate! {
    pub fn bst_invariant(&self) -> bool {
        if let Tree::Node(value, left, right) = self {
            // Could turn this into a single `forall` if we wanted?
            forall(|i: &T| left.contains(i) == (matches!(i.cmp(value), Greater) && self.contains(i))) &&
            forall(|i: &T| right.contains(i) == (matches!(i.cmp(value), Less) && self.contains(i))) &&
            left.bst_invariant() && right.bst_invariant()
        } else { true }
    }
    }

    #[ensures(self.contains(&new_value))]
    #[ensures(forall(|i: &T| !matches!(new_value.cmp(i), Equal) ==> old(self.contains(i)) == self.contains(i)))]
    pub fn insert(&mut self, new_value: T) {
        if let Tree::Node(value, left, right) = self {
            match new_value.cmp(value) {
                Equal => (),
                Less => left.insert(new_value),
                Greater => right.insert(new_value),
            }
        } else {
            *self = Tree::Node(new_value, Box::new(Tree::Empty), Box::new(Tree::Empty))
        }
    }
}
