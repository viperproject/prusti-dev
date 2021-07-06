fn main() {
    let _: *const i32 = std::ptr::null_mut();   //~ ERROR raw pointers are not supported
}