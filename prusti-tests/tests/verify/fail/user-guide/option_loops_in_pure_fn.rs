// ignore-test: This code causes Prusti to panic
// The next and previous line are only required for (doc)tests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

pub struct List {
    head: Link,
}

type Link = Option<Box<Node>>;

struct Node {
    elem: i32,
    next: Link,
}

//// ANCHOR: code
impl List {
    // Prusti cannot verify these functions at the moment,
    // since loops in pure functions are not yet supported:
    #[pure]
    pub fn len(&self) -> usize {
        let mut curr = &self.head;
        let mut i = 0;
        while let Some(node) = curr {
            body_invariant!(true);
            i += 1;
            curr = &node.next;
        }
        i
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        let mut curr = &self.head;
        let mut i = index;
        while let Some(node) = curr {
            body_invariant!(true);
            if i == 0 {
                return node.elem;
            }
            i -= 1;
            curr = &node.next;
        }
        unreachable!()
    }
}
//// ANCHOR_END: code