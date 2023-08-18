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

//// ANCHOR: initial_code
impl List {
    pub fn push(&mut self, elem: i32) {
        let new_node = Box::new(Node {
            elem, // we can use `elem` instead of `elem: elem,` here, since the variable has the same name as the field
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }
    //// ANCHOR_END: initial_code

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
    //// ANCHOR: initial_code
}
//// ANCHOR_END: initial_code

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
