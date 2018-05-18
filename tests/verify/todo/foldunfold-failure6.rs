//! Example: paths with enums

extern crate prusti_contracts;

struct A;
enum B {
    B1 { a1: A, a2: A },
    B2 { a1: A, a2: A }
}

fn main() {
    let b = B::B1 { a1: A, a2: A };

    match b {
        B::B1 { ref a1, ref a2 } => {}, // borrows have a cast in the path
        B::B2 { ref a1, ref a2 } => {}  // borrows have a cast in the path
    }
}
