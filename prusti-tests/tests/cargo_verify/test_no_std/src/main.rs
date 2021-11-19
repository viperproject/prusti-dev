#![feature(lang_items)]
#![no_std]
#![no_main]

extern crate libc;
extern crate prusti_contracts;

use prusti_contracts::*;

#[requires(true)]
#[ensures(true)]
pub fn test() {}

#[lang = "eh_personality"]
#[no_mangle]
pub extern fn rust_eh_personality() {}

#[lang = "panic_impl"]
#[no_mangle]
#[trusted]
pub extern fn rust_begin_panic(_info: &core::panic::PanicInfo) -> ! {
    // SAFETY: this program has no open streams or active locks, so this is safe.
    unsafe { libc::abort() }
}

#[no_mangle]
#[trusted]
extern "C" fn main(_argc: isize, _argv: *const *const u8) -> isize {
    0
}
