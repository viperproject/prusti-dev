//// ANCHOR: types
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
//// ANCHOR_END: types

//// ANCHOR: code
fn main() {
    let test = Node {
        elem: 17,
        next: Link::Empty,
    };

    if test.elem > 23 {
        panic!() // unreachable
    }
}
//// ANCHOR_END: code
