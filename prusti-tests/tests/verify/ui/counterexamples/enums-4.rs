// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

struct SomeStruct {
    a: SomeEnum,
    b: SomeEnum,
}

enum SomeEnum {
    One,
    Two,
    Three,
}

enum OtherEnum {
    One(SomeEnum),
    Two(SomeEnum, SomeEnum),
}

#[ensures(result)]
fn test1(x: SomeStruct) -> bool {
    match x.a {
        SomeEnum::One => match x.b {
            SomeEnum::Two => false,
            _ => true,
        },
        _ => true,
    }
}

#[ensures(result)]
fn test2(x: &SomeEnum) -> bool {
    match *x {
        SomeEnum::One => false,
        _ => true,
    }
}

#[ensures(result)]
fn test3(x: OtherEnum) -> bool {
    match x {
        OtherEnum::One(y) => true,
        OtherEnum::Two(a, b) => match a {
            SomeEnum::One => match b {
                SomeEnum::Two => false,
                _ => true,
            },
            _ => true,
        },
        _ => true,
    }
}

fn main() {}
