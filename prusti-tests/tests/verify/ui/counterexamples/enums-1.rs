// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

enum SecondEnum {
    One,
    Two,
}

enum OneOfFive {
    One(i32),
    Two(i32, i32),
    Three { x: i32, y: char, z: usize },
    Four(i32, char, bool, bool),
    Five { a: i32, b: bool, c: i32, d: char, e: bool },
}

#[requires(matches!(x, OneOfFive::Five { a: 1, b: _, c: 2, d: _, e: false }))]
#[ensures(result)]
fn test1(x: OneOfFive, y: SecondEnum) -> bool {
    match x {
        OneOfFive::One(_) => true,
        OneOfFive::Five { a, b, c, d, e } => match y {
            SecondEnum::One => !b || d != 'd',
            _ => true,
        },
        _ => true,
    }
}

fn main() {}
