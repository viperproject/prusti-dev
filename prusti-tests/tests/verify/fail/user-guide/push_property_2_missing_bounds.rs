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

#[extern_spec(std::mem)]
#[ensures(snap(dest) === src)]
#[ensures(result === old(snap(dest)))]
fn replace<T>(dest: &mut T, src: T) -> T;

//// ANCHOR: lookup
impl List {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        self.head.lookup(index)
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(0) == elem)] // 2. Property //~ ERROR postcondition might not hold
    pub fn push(&mut self, elem: i32) {
        // ...
        //// ANCHOR_END: lookup
        let new_node = Box::new(Node {
            elem,
            next: std::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new_node);
    }

    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
        //// ANCHOR: lookup
    }
}

impl Link {
    #[pure]
    pub fn lookup(&self, index: usize) -> i32 {
        match self {
            Link::More(node) => {
                if index == 0 {
                    node.elem
                } else {
                    node.next.lookup(index - 1)
                }
            }
            Link::Empty => unreachable!(), //~ ERROR: unreachable!(..) statement might be reachable
        }
    }
    //// ANCHOR_END: lookup

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
    //// ANCHOR: lookup
}
//// ANCHOR_END: lookup
