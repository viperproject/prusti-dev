use prusti_contracts::*;

extern "C" {
    fn max(a: i32, b: i32) -> i32;

    fn unannotated();

    fn abs(a: i32) -> i32;
}

#[extern_spec(crate)]
extern "C" {
    #[ensures(a >= b ==> result = a)]
    #[ensures(b >= a ==> result == b)]
    fn max(a: i32, b: i32) -> i32;

    fn unannotated();

    #[ensures(a < 0 ==> result == -a)]
    #[ensures(a >= 0 ==> result = a)]
    fn abs(a: i32) -> i32;
}

fn main() {}