// From the libc crate

#![allow(dead_code)]

pub const FD_SETSIZE: usize = 1024;

#[allow(non_camel_case_types)]
pub struct fd_set {
    #[cfg(target_pointer_width = "64")]
    fds_bits: [i64; FD_SETSIZE / 64],
    #[cfg(target_pointer_width = "32")]
    fds_bits: [i32; FD_SETSIZE / 32],
}

pub fn test(x: fd_set) -> fd_set {
    x
}

fn main(){}
