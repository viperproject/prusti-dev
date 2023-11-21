use prusti_contracts::*;

pub struct Empty;
pub struct Tuple<T>(Empty, (bool, T, i8), Fields);
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
    let a = Tuple::test(-127, 11);
    check(a.field_1 == 0);
    check_pure(a.field_1 == 0);
}

impl<T: Copy> Tuple<T> {
    // #[pure]
    // pub fn get_field_1(self) -> i32 {
    //     self.2.field_1
    // }

    #[trusted]
    #[pure]
    // #[ensures(result.0 === self)]
    // #[ensures(result.1 === self)]
    pub fn duplicate(self) -> (Self, Self) { todo!() }

    #[pure]
    pub fn get_f1_nested(self) -> u32 {
        self.2.field_1
    }
    #[pure]
    pub fn get_f1(self) -> u32 {
        self.get_f1_nested()
    }

    // #[ensures(result.0 != result.1.get_field_1())]
    #[requires(x != -128)]
    #[ensures(result.field_1 == 0)]
    #[ensures(result === result)]
    #[ensures(forall(|i: u32| i >= result.get_field_1() ==> i >= i))]
    pub fn test(x: i8, y: T) -> Fields {
        let t = Tuple(Empty, (true, y, -x), Fields { field_1: 0, field_2: () });
        let value = t.get_f1();
        check(value == 0);
        // let f = t0.get_field_1();
        Fields { field_1: 0, field_2: () }
    }
}

impl Fields {
    #[pure]
    pub fn get_field_1(self) -> u32 {
        self.field_1
    }
}

#[repr(i8)]
enum Enum {
    VariantA = 0,
    VariantB(Fields, Option<bool>) = -128,
    VariantC {
        field_1: u32,
        field_2: (),
    } = 127,
}
pub fn enum_test(e: Enum, v: u8) {
    match v {
        0 => {
            let value = match e {
                Enum::VariantA => {
                    0
                }
                Enum::VariantB(f, _) => {
                    f.field_1
                }
                Enum::VariantC { field_1, field_2 } => {
                    field_1
                }
            };
        }
        1 => {
            let Enum::VariantB(a, b) = e else {
                return;
            };
        }
        2 => {
            if let Enum::VariantC { field_1, field_2 } = e {
                
            } else {
                return;
            }
        }
        _ => {
            return;
        }
    }
}
