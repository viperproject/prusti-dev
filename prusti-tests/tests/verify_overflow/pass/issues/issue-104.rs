use prusti_contracts::*;

#[pure]
#[trusted]
#[requires(x >= 0)]
fn foo_u32(x: u32) -> u32 {
    unimplemented!()
}

#[pure]
#[trusted]
#[requires(x >= 0)]
fn foo_u64(x: u64) -> u64 {
    unimplemented!()
}

#[pure]
#[trusted]
#[requires(x >= 0)]
fn foo_usize(x: usize) -> usize {
    unimplemented!()
}

#[pure]
fn test_u32_ge_zero(x: u32) -> u32 {
    foo_u32(x)
}

#[pure]
fn test_u64_ge_zero(x: u64) -> u64 {
    foo_u64(x)
}

#[pure]
fn test_usize_ge_zero(x: usize) -> usize {
    foo_usize(x)
}

pub fn test() {
    assert!(test_u32_ge_zero(123) >= 0);
    assert!(test_u64_ge_zero(123) >= 0);
    assert!(test_usize_ge_zero(123) >= 0);
}

fn main() {
}
