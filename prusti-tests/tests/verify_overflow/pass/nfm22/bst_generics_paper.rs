// compile-flags: -Penable_type_invariants=true
use prusti_contracts::*;
use std::cmp::{Ord, Ordering::{self, Equal, Less, Greater}};

fn main() {
    let mut t = Tree::Empty;
    t.insert(0);
    if let Tree::Node(value, left, right) = &t {
        assert!(matches!(**left, Tree::Empty));
        assert!(matches!(**right, Tree::Empty));
        assert!(*value == 0);
    } else {
        unreachable!()
    }
}

#[invariant(self.bst_invariant())]
pub enum Tree<T: Ord> {
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
    Empty,
}

#[extern_spec]
impl Ord for i32 {
    #[pure]
    #[ensures(matches!(result, Equal) == (*self == *other))]
    #[ensures(matches!(result, Less) == (*self < *other))]
    #[ensures(matches!(result, Greater) == (*self > *other))]
    fn cmp(&self, other: &Self) -> Ordering;
}

#[extern_spec]
trait Ord {
    #[pure]
    #[ensures(match (result, other.cmp(self)) {
        (Equal, Equal) |
        (Less, Greater) |
        (Greater, Less) => true,
        _ => false,
    })]
    #[ensures(forall(|x: &Self| match (result, other.cmp(x), self.cmp(x)) {
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
            forall(|i: &T| left.contains(i) == (matches!(i.cmp(value), Less) && self.contains(i))) &&
            forall(|i: &T| right.contains(i) == (matches!(i.cmp(value), Greater) && self.contains(i)))
        } else { true }
    }
    }

    #[ensures(self.contains(old(&new_value)))]
    #[ensures(forall(|i: &T| !matches!(old(new_value).cmp(i), Equal) ==> self.contains(i) == old(self).contains(i)))]
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

    #[requires(matches!(self, Tree::Node(..)))]
    #[assert_on_expiry(
        // Must hold before result can expire
        if let Tree::Node(_, left, right) = old(self) {
            forall(|i: &T| left.contains(i) ==> matches!(i.cmp(result), Less)) &&
            forall(|i: &T| right.contains(i) ==> matches!(i.cmp(result), Greater))
        } else { false },
        // A postcondition of `get_root_value` after result expires
        if let Tree::Node(ref value, _, _) = self {
            matches!(value.cmp(before_expiry(result)), Equal)
        } else { false }
    )]
    pub fn get_root_value(&mut self) -> &mut T {
        if let Tree::Node(value, _, _) = self { value } else { panic!() }
    }
}
