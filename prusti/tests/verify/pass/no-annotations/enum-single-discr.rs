extern crate prusti_contracts;

enum MyEnum {
    A = 123
}

fn main() {
    let a = MyEnum::A;

    match a {
        MyEnum::A => { return; } // OK
    }

    unreachable!();
}
