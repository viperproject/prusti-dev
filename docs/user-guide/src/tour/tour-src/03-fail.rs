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

fn main() {
    let test = Node {
        elem: 17,
        next: Link::Empty,
    };

    if test.elem > 23 {
        panic!() // unreachable
    }
}

fn test(x: i32) {
    let test = Node {
        elem: x, // unknown value
        next: Link::Empty,
    };

    if test.elem > 23 {
        panic!()
    }
}
