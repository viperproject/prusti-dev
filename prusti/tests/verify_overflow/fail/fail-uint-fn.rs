extern crate prusti_contracts;

#[pure]
fn test_u32_ge_zero(x: u32) -> u32 {
    -x //~ ERROR
}

#[pure]
fn test_u64_ge_zero(x: u64) -> u64 {
    -x //~ ERROR
}

#[pure]
fn test_usize_ge_zero(x: usize) -> usize {
    -x //~ ERROR
}

fn main() {}
