fn foo<T: Ord> (bar: &mut [T]) {
    let _ = bar[0] == bar[0];   //~ ERROR type parameters in arrays are not supported
}

fn main() {}