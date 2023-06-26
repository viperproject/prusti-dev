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

impl List {
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List {
            head: Link::Empty,
        }
    }
}

//// ANCHOR: implementation
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
//// ANCHOR_END: implementation

//// ANCHOR: test_len
fn test_len(link: &Link) {
    let link_is_empty = link.is_empty();
    let link_len = link.len();
    assert!(link_is_empty == (link_len == 0));
}
//// ANCHOR_END: test_len

//// ANCHOR: nothing
//// ANCHOR_END: nothing