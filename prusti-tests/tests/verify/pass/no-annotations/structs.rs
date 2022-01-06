struct MyStruct {
    a: i32,
    b: (i32, i32)
}

fn foo<'a>(arg: MyStruct) -> (i32, i32) {
    let mut x = MyStruct { a: 111, b: (222, 333) };
    x.b.0 = 444;
    let y = x;
    let z = MyStruct { a: 555, b: (666, 777) };
    y.b
}

fn main() {
}
