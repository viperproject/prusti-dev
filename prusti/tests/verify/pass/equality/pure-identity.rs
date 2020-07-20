extern crate prusti_contracts;

#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(x: A) -> A {
    x
}

fn test(x: A) {
    let zx = get_value(x);
    //let zy = get_value(x);
}

fn main() {
}

