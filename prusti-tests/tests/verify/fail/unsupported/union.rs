union Foo {
    a: [i32; 1],
    b: [i32; 1],
}

fn main() {
    let _ = Foo { a: [0] }; //~ ERROR unions are not supported
}
