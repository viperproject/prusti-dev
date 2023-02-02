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

//// ANCHOR: first_spec_1
impl List {
    pub fn len(&self) -> usize {
        self.head.len()
    }
//// ANCHOR_END: first_spec_1

//// ANCHOR: first_spec_2
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
//// ANCHOR_END: first_spec_2
//// ANCHOR: first_spec_1
}

impl Link {
    fn len(&self) -> usize {
        0
    }
}
//// ANCHOR_END: first_spec_1