// compile-flags: -Psif=true

use prusti_contracts::*;

fn declassify_int(i: i32) {
    declassify!(i);
}

fn declassify_bool(b: bool) {
    declassify!(b);
}

fn declassify_mod(i: i32) {
    declassify!(i % 2);
}

fn main() {}
