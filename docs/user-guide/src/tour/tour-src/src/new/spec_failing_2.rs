//// ANCHOR: import_prusti
use prusti_contracts::*;

//// ANCHOR_END: import_prusti
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

//// ANCHOR: import_prusti
impl List {
//// ANCHOR_END: import_prusti
    pub fn len(&self) -> usize {
        self.head.len()
    }

//// ANCHOR: import_prusti
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
}
//// ANCHOR_END: import_prusti

impl Link {
    fn len(&self) -> usize {
        0
    }
}