extern crate prusti_contracts;

struct U {
    f: u32,
}

fn test1(a: &mut U, value: u32) {   //~ ERROR implicit type invariants might not hold at the end of the method.
    a.f -= value;
}

fn test2(a: &mut U) -> &mut u32 { //~ ERROR implicit type invariants might not hold at the end of the method.
    a.f -= 5;
    &mut a.f
}

fn main() {}
