extern crate prusti_contracts;
mod functions {
    use prusti_contracts::*;
    
    // #[extern_spec({"ffi.c"}crate)]
    #[extern_spec(crate)]
    extern "C" {
        #[ensures (result == a + b)]
        pub fn add(a: i32, b: i32) -> i32;
    }

    extern "C" {
        // #[ensures (result == a + b)]
        pub fn add(a: i32, b: i32) -> i32;

        pub fn fun(a: &i32, b: &i32) -> i32;
    }
}

use functions::add;

fn main() {
    let s = 11;
    let a = unsafe { add(s, 5) };
    assert!(a == s + 5);
}
