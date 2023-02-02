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

impl List {
    #[pure]
    pub fn len(&self) -> usize {
        self.head.len()
    }

    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
}

//// ANCHOR: pure_annotation
impl Link {
    #[pure]
    fn len(&self) -> usize {
        0
    }
}
//// ANCHOR_END: pure_annotation