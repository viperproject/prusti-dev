#![feature(c_variadic)]
unsafe extern "C" fn func(i: i32, mut args: ...) {} //~ ERROR variadic functions are not supported

fn main() {
    unsafe{func(0, 0);} //~ ERROR variadic functions are not supported
}
