use prusti_contracts::*;

#[pure]
#[trusted]
fn get_usize() -> usize {
    unimplemented!();
}

#[pure]
#[trusted]
fn get_u32() -> u32 {
    unimplemented!();
}

#[pure]
#[trusted]
fn get_i32() -> i32 {
    unimplemented!();
}

fn test1() {
    assert!(get_usize() >= 0);
    assert!(get_u32() >= 0);
}

fn test3(x: usize, y: u32, z: i32) {
    assert!(x >= 0);
    assert!(y >= 0);
}

fn main() {}
