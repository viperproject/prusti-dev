/// An adaptation of the example from
/// https://rosettacode.org/wiki/Mutual_recursion#Rust

use prusti_contracts::*;

#[ensures(n == 0 ==> result == 1)]
#[ensures(n >= 1 ==> n >= result)]
fn f(n: u32) -> u32 {
    match n {
        0 => 1,
        _ => n - m(f(n - 1))
    }
}

#[ensures(n >= result)]
fn m(n: u32) -> u32 {
    match n {
        0 => 0,
        _ => n - f(m(n - 1))
    }
}

#[trusted]
fn print_u32(number: u32) {
    print!("{} ", number);
}

#[trusted]
fn print_newline() {
    println!("");
}

fn main() {
    let mut i = 0;
    while i < 20 {
        body_invariant!(i < 20);
        let res = f(i);
        print_u32(res);
        i += 1;
    }
    print_newline();
    let mut i = 0;
    while i < 20 {
        body_invariant!(i < 20);
        let res = m(i);
        print_u32(res);
        i += 1;
    }
    print_newline();
}
