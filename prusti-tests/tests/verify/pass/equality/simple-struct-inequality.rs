#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

fn main() {
    let _a = A { i: 17 };
    let _b = A { i: 42 };
    assert!(_a != _b);
}
