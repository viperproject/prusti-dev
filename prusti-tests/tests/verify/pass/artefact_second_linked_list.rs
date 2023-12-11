// compile-flags: -Puse_more_complete_exhale=false

#![feature(box_patterns)]

//! An adaptation of the example from
//! https://rust-unofficial.github.io/too-many-lists/second-final.html
//!
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Add additional functions for capturing functional specification.
//! +   Replace `assert_eq!` with supported ones.
//! +   Rewrite to not use closures and higher-order functions.
//!
//! Verified methods:
//!
//! +   `new`
//! +   `push`
//! +   `pop`
//!
//! Added new verified methods:
//!
//! +   `index`
//! +   `index_mut`
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Push and pop behaves correctly.

use prusti_contracts::*;

pub struct List<T> {
    head: Link<T>,
}

#[pure]
fn is_some<T>(s: &Option<T>) -> bool {
    matches!(s, Some(_))
}

#[pure]
fn is_none<T>(s: &Option<T>) -> bool {
    matches!(s, None)
}

#[trusted]
#[ensures(
    is_none(option) &&
    *old(option) === result
)]
fn take<T>(option: &mut Option<T>) -> Option<T> {
    option.take()
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: None }
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(forall(|i: usize| 0 < i && i < self.len() ==> 
        self.index(i) === old(self.index(i-1))
    ))]
    #[ensures(*self.index(0) === elem)]
    pub fn push(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem: elem,
            next: take(&mut self.head),
        });

        self.head = Some(new_node);
    }

    #[ensures(if old(self.len()) == 0 {
        self.len() == 0 &&
        is_none(&result)
    } else {
        self.len() == old(self.len()) - 1 &&
        forall(|i: usize| (0 <= i && i < self.len()) ==>
               self.index(i) === old(self.index(i+1)),
               triggers=[(self.index(i),),]) &&
        match result {
            Some(r) => r === *old(self.index(0)),
            _ => false,
        }
    })]
    pub fn pop(&mut self) -> Option<T> {
        if let Some(node) = take(&mut self.head) {
            self.head = node.next;
            Some(node.elem)
        } else {
            None
        }
    }

    #[pure]
    pub fn len(&self) -> usize {
        match &self.head {
            Some(node) => node.len(),
            None => 0,
        }
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn index(&self, index: usize) -> &T {
        match &self.head {
            Some(node) => node.index(index),
            None => unreachable!(),
        }
    }

    #[requires(0 <= index && index < self.len())]
    #[ensures(&*result === old(self.index(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        forall(|i: usize| 0 <= i && i < self.len() && i != index ==>
               self.index(i) === old(self.index(i))
        ) &&
        self.index(index) === before_expiry(result)
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        match self.head {
            Some(box ref mut node) => node.index_mut(index),
            None => unreachable!(),
        }
    }
}

impl<T> Node<T> {
    #[pure]
    pub fn len(&self) -> usize {
        1 + match &self.next {
            Some(next) => next.len(),
            None => 0,
        }
    }

    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn index(&self, index: usize) -> &T {
        if index == 0 {
            &self.elem
        } else {
            match &self.next {
                Some(next) => next.index(index-1),
                None => unreachable!(),
            }
        }
    }

    #[requires(0 <= index && index < self.len())]
    #[ensures(&*result === old(self.index(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        forall(|i: usize| 0 <= i && i < self.len() && i != index ==>
               self.index(i) === old(self.index(i))
        ) &&
        self.index(index) === before_expiry(result)
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        if index == 0 {
            &mut self.elem
        } else {
            match self.next {
                Some(box ref mut next) => next.index_mut(index-1),
                None => unreachable!(),
            }
        }
    }
}

mod test {
    use super::List;

    use prusti_contracts::*;

    fn basics() {
        let mut list = List::new();

        // Check empty list behaves right
        assert!(matches!(list.pop(), None));

        // Populate list
        list.push(1);
        list.push(2);
        list.push(3);

      //prusti_assert!(list.len() == 3);
      //prusti_assert!(*list.index(0) == 3);
      //prusti_assert!(*list.index(1) == 2);
      //prusti_assert!(*list.index(2) == 1);

        // Check normal removal
        assert!(matches!(list.pop(), Some(3)));
      //prusti_assert!(list.len() == 2);
      //prusti_assert!(*list.index(0) == 2);
      //prusti_assert!(*list.index(1) == 1);
        assert!(matches!(list.pop(), Some(2)));
      //prusti_assert!(*list.index(0) == 1);

        // Push some more just to make sure nothing's corrupted
        list.push(4);
        list.push(5);

      //prusti_assert!(*list.index(0) == 5);
      //prusti_assert!(*list.index(1) == 4);
      //prusti_assert!(*list.index(2) == 1);

        // Check normal removal
        assert!(matches!(list.pop(), Some(5)));
        assert!(matches!(list.pop(), Some(4)));

        // Check exhaustion
        assert!(matches!(list.pop(), Some(1)));
        assert!(matches!(list.pop(), None));
    }

}

fn main() {}
