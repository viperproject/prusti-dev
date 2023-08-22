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
//// ANCHOR_END: extern_spec

//// ANCHOR: property_1
impl List {
    #[ensures(self.len() == old(self.len()) + 1)] // 1. Property
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }
    //// ANCHOR_END: property_1

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
    //// ANCHOR: property_1
}
//// ANCHOR_END: property_1

impl Link {
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
