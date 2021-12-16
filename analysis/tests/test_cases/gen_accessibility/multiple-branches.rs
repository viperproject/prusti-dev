struct MyStruct {
    a: i32,
    b: (i32, i32)
}

fn foo(switch: bool) -> MyStruct {
    let mut x = MyStruct { a: 000, b: (000, 000) };
    let y = MyStruct { a: 111, b: (222, 333) };
    if switch {
        return x
    }
    if switch {
        x.b.0 = 444;
    }
    if switch {
        x.b.1 = 555;
    }
    if switch {
        return x
    }
    if switch {
        x.a = 666;
    }
    if switch {
        x.b = (777, 888);
    }
    if switch {
        return x
    }
    if switch {
        x.a = y.a;
    }
    if switch {
        x.b = y.b;
    }
    if switch {
        x.b.0 = 999;
    }
    let z = x;
    z
}
