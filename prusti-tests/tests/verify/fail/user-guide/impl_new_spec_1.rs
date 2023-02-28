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

//// ANCHOR: first_spec_1
//// ANCHOR: first_spec_2
impl List {
    //// ANCHOR_END: first_spec_2
    pub fn len(&self) -> usize {
        self.head.len()
    }
//// ANCHOR_END: first_spec_1

//// ANCHOR: first_spec_2
    #[ensures(result.len() == 0)] //~ ERROR use of impure function "List::len" in pure code is not allowed
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
//// ANCHOR: first_spec_1
}
//// ANCHOR_END: first_spec_2

impl Link {
    fn len(&self) -> usize {
        0
    }
}
//// ANCHOR_END: first_spec_1