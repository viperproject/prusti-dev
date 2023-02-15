use prusti_contracts::*;

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
        self.head.len()
    }
//// ANCHOR_END: pure_annotation

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
}

impl Link {
    fn len(&self) -> usize {
        0
    }
}