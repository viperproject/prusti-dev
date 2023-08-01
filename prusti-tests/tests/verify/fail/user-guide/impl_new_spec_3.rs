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

//// ANCHOR: pure_annotation
impl List {
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len() //~ ERROR use of impure function "Link::len" in pure code is not allowed
    }
//// ANCHOR_END: pure_annotation

    #[ensures(result.len() == 0)] //~ ERROR precondition of pure function call might not hold.
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
    //// ANCHOR: pure_annotation
}
//// ANCHOR_END: pure_annotation

impl Link {
    fn len(&self) -> usize {
        0
    }
}