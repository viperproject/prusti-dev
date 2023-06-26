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

//// ANCHOR: impl_new
impl List {
    pub fn new() -> Self {
        List { head: Link::Empty }
    }
}
//// ANCHOR_END: impl_new