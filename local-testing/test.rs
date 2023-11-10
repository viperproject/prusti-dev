use prusti_contracts::*;

pub struct Empty;
pub struct Tuple(Empty, (bool, u8, i8), Fields);
pub struct Fields {
    pub field_1: u32,
    pub field_2: (),
}

#[requires(b)]
#[ensures(result == b)]
pub fn check(b: bool) -> bool { b }

#[pure]
#[requires(b)]
#[ensures(result == b)]
pub fn check_pure(b: bool) -> bool { b }

pub fn main() {
    let a = Tuple::test(-127);
    check(a == 0);
    check_pure(a == 0);
}

impl Tuple {
    // #[pure]
    // pub fn get_field_1(self) -> i32 {
    //     self.2.field_1
    // }

    #[trusted]
    #[pure]
    // #[ensures(result.0 === self)]
    // #[ensures(result.1 === self)]
    pub fn duplicate(self) -> (Self, Self) { todo!() }

    // #[ensures(result.0 != result.1.get_field_1())]
    #[requires(x != -128)]
    #[ensures(result == 0)]
    pub fn test(x: i8) -> i32 {
        let t = Tuple(Empty, (true, 11, -x), Fields { field_1: 0, field_2: () });
        let (t0, t1) = t.duplicate();
        // let f = t0.get_field_1();
        0
    }
}
