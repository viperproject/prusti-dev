// ignore-test The function arguments (desugared to a 1-tuple of reference
//             here) are probably the issue; then this is similar to #1077 ?

pub fn max_by_key<A, B: Ord>(a: A, b: A, key: impl Fn(&A) -> B) -> A {
    if key(&a) > key(&b) { //~ Error: only calls to closures are supported
        a
    } else {
        b
    }
}

fn main() {}
