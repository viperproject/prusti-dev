fn foo(p: *const i32) {
    let _ = p.is_null();    //~ ERROR raw pointers are not supported
}

fn main() {
    let _: *const i32 = std::ptr::null_mut();   //~ ERROR raw pointers are not supported
}
