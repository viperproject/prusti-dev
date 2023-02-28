//// ANCHOR: none
//// ANCHOR_END: none
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

pub struct List {
    head: Link,
}

enum Link {
    Empty,
    More(Box<Node>),
}

struct Node {
    elem: i32,
    next: Link,
}

//// ANCHOR: extern_spec
#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;

// Specs for std::option::Option<T>::unwrap(self) (and others) can be found here (work in progress):
// https://github.com/viperproject/prusti-dev/pull/1249/files#diff-bccda07f8a48357687e26408251041072c7470c188092fb58439de39974bdab5R47-R49

#[extern_spec]
impl<T> std::option::Option<T> {
    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    pub fn unwrap(self) -> T;

    #[pure]
    #[ensures(result == matches!(self, None))]
    pub const fn is_none(&self) -> bool;

    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    pub const fn is_some(&self) -> bool;
}
//// ANCHOR_END: extern_spec

//// ANCHOR: two_state_predicate
//// ANCHOR: predicate_use
//// ANCHOR: try_pop_empty
//// ANCHOR: pop_result_correct
//// ANCHOR: try_pop_result_correct
impl List {
    //// ANCHOR_END: two_state_predicate
    //// ANCHOR_END: predicate_use
    //// ANCHOR_END: try_pop_empty
    //// ANCHOR_END: pop_result_correct
    //// ANCHOR_END: try_pop_result_correct
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[pure]
    fn is_empty(&self) -> bool {
        self.head.is_empty()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)]
    #[ensures(forall(|i: usize| (i < old(self.len())) ==>
                 old(self.lookup(i)) == self.lookup(i + 1)))]
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    //// ANCHOR: two_state_predicate
    predicate! {
        // two-state predicate to check if the head of a list was correctly removed
        fn head_removed(&self, prev: &Self) -> bool {
            self.len() == prev.len() - 1 // The length will decrease by 1
            && forall(|i: usize| // Every element will be shifted forwards by one
                (1 <= i && i < prev.len())
                    ==> prev.lookup(i) == self.lookup(i - 1))
        }
    }
    //// ANCHOR_END: two_state_predicate

    //// ANCHOR: try_pop_empty
    #[ensures(old(self.is_empty()) ==>
        result.is_none() &&
        self.is_empty()
    )]
    //// ANCHOR_END: try_pop_empty
    //// ANCHOR: predicate_use
    //// ANCHOR: try_pop_result_correct
    #[ensures(!old(self.is_empty()) ==>
        //// ANCHOR_END: try_pop_result_correct
        self.head_removed(&old(snap(self)))
        //// ANCHOR_END: predicate_use
        &&
        //// ANCHOR: try_pop_result_correct
        result === Some(old(snap(self)).lookup(0))
        //// ANCHOR: predicate_use
    )]
    //// ANCHOR: try_pop_empty
    pub fn try_pop(&mut self) -> Option<i32> {
        // ...
        //// ANCHOR_END: try_pop_empty
        //// ANCHOR_END: predicate_use
        //// ANCHOR_END: try_pop_result_correct
        match std::mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
        //// ANCHOR: predicate_use
    }

    //// ANCHOR_END: predicate_use
    #[requires(!self.is_empty())]
    //// ANCHOR: predicate_use
    #[ensures(self.head_removed(&old(snap(self))))]
    //// ANCHOR_END: predicate_use
    //// ANCHOR: pop_result_correct
    #[ensures(result === old(snap(self)).lookup(0))]
    //// ANCHOR: predicate_use
    pub fn pop(&mut self) -> i32 {
        // ...
        //// ANCHOR_END: predicate_use
        //// ANCHOR_END: pop_result_correct
        self.try_pop().unwrap()
        //// ANCHOR: try_pop_empty
        //// ANCHOR: pop_result_correct
        //// ANCHOR: try_pop_result_correct
        //// ANCHOR: predicate_use
    }
    //// ANCHOR: two_state_predicate
}
//// ANCHOR_END: two_state_predicate
//// ANCHOR_END: predicate_use
//// ANCHOR_END: try_pop_empty
//// ANCHOR_END: pop_result_correct
//// ANCHOR_END: try_pop_result_correct

impl Link {
    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
            Link::Empty => unreachable!(),
        }
    }

    #[pure]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(node) => 1 + node.next.len(),
        }
    }

    #[pure]
    fn is_empty(&self) -> bool {
        matches!(self, Link::Empty)
    }
}
