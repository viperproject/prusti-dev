pub fn max_by_key<A, B: Ord>(a: A, b: A, key: impl Fn(&A) -> B) -> A {
    if key(&a) > key(&b) { //~ Error: only calls to closures are supported
        a
    } else {
        b
    }
}

fn main() {}
