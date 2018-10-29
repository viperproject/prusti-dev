//! Example: paths with enums

struct A;
enum B {
    B1 { a1: A, a2: A },
    B2 { a1: A, a2: A }
}

fn main() {
    let b = B::B1 { a1: A, a2: A };

    match b {
        B::B1 { ref a1, ref a2 } => {},
        B::B2 { ref a1, ref a2 } => {}
    }
}
