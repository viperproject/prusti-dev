fn foo(args: impl IntoIterator<Item = u32>) { drop(args) }
fn main() {}
