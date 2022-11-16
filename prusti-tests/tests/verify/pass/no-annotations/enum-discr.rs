enum MyEnum {
    A = 123,
    B = 11,
    C,
    D,
    E
}

fn main() {
    let a = MyEnum::A;
    let b = MyEnum::B;
    let e = MyEnum::E;

    match a {
        MyEnum::A => {} // OK
        _ => unreachable!(),
    }

    match (b, e) {
        (MyEnum::B, MyEnum::E) => {} // OK
        _ => unreachable!(),
    }
}
