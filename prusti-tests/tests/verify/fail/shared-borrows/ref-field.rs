use prusti_contracts::*;

struct T {
    v: u32,
}

struct U<'a> {
    /// The following reference-typed field is never used in the program.
    f: &'a T,
    v: u32,
}

#[pure]
#[requires(x.v == 123)]
#[ensures(x.v == 123)]
fn pure_get_field(x: &U) -> u32 {
    x.v
}

fn test_wrong_precondition_pure(x: &U) -> u32 {
    pure_get_field(x) //~ ERROR precondition of pure function call might not hold
}

#[requires(x.v == 123)]
#[ensures(x.v == 456)] //~ ERROR postcondition might not hold
fn test_wrong_postcondition_pure(x: &U) -> u32 {
    pure_get_field(x)
}

#[requires(x.v == 123)]
#[ensures(x.v == 123)]
fn get_field(x: &U) -> u32 {
    x.v
}

fn test_wrong_precondition(x: &U) -> u32 {
    get_field(x) //~ ERROR precondition might not hold
}

#[requires(x.v == 123)]
#[ensures(x.v == 456)] //~ ERROR postcondition might not hold
fn test_wrong_postcondition(x: &U) -> u32 {
    get_field(x)
}

fn main() {}
