//! An adaptation of the example from
//! https://rosettacode.org/wiki/Singly-linked_list/Element_definition#Rust
//! https://rosettacode.org/wiki/Singly-linked_list/Traversal#Rust
//! https://rosettacode.org/wiki/Singly-linked_list/Element_insertion#Rust
//!
//! Omitted because uses reference-typed fields:
//!
//! +   Iteration by immutable reference
//! +   Iteration by mutable reference
//!
//! Changes:
//!
//! +   Replaced application of the `map` function in `next` with an
//!     explicit `match` statement.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//!

use prusti_contracts::*;

type Link<T> = Option<Box<Node<T>>>; // Type alias
pub struct List<T> { // User-facing interface for list
    head: Link<T>,
}

struct Node<T> { // Private implementation of Node
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    pub fn new() -> Self { // List constructor
        List { head: None }
    }
    pub fn push(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem: elem,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
}

pub struct IntoIter<T>(List<T>);
 
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        match self.0.head.take() {
            Some(node) => {
                let node = *node;
                self.0.head = node.next;
                Some(node.elem)
            }
            None => {
                None
            }
        }
    }
}

pub fn test() {
    let mut list = List::new();
    list.push(5);
}

fn main() {}
