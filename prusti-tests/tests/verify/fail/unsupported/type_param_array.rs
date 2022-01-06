fn foo<T: Ord> (bar: &mut [T]) {
    let _ = bar[0] == bar[0];   //~ ERROR type is not supported
}

fn main() {}
