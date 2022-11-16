use prusti_contracts::*;

fn reborrow<T>(x: &mut T) -> &mut T {
    x
}

pub fn test1() {
    let mut a = 6;
    let x = reborrow(&mut a);
    *x = 4;
}

fn main() {}
