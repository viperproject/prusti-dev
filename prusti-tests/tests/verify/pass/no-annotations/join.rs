struct MyStruct {
    a: i32,
    b: (i32, i32)
}

fn foo<'a>(mut x: MyStruct, switch: bool) -> MyStruct {
    if switch {
        // Unfold MyStruct
        x.b = (444, 555);
    } else {
        // Nothing
    }
    // Join branches
    x
}

fn main() {
}
