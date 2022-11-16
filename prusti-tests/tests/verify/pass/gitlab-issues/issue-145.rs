use prusti_contracts::*;

pub enum Void { }

pub fn unreachable(x: Void) -> ! {
    match x {}
}

#[trusted]
fn create_void() -> Void {
    unimplemented!();
}

fn test() {
    let x = create_void();
    match x {};
    assert!(false);
}

fn main() {
}
