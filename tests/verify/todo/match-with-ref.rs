//! Example: match that uses a reference internally

#![feature(nll)]

extern crate prusti_contracts;

enum OptionInt {
    Some(i32),
    None,
}

fn none_or_positive(x: OptionInt) -> bool {
    match x {
        OptionInt::None => true,
        OptionInt::Some(val) if val > 0 => true,
        OptionInt::Some(val) => false,
    }
}

fn main() {}
