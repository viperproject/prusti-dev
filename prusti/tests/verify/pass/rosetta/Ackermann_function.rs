/// An adaptation of the example from
/// https://rosettacode.org/wiki/Ackermann_function#Rust

extern crate prusti_contracts;

#[pure]
fn ack_pure(m: isize, n: isize) -> isize {
    if m == 0 {
        n + 1
    } else if n == 0 {
        ack_pure(m - 1, 1)
    } else {
        ack_pure(m - 1, ack_pure(m, n - 1))
    }
}


#[ensures="result == ack_pure(m, n)"]
fn ack1(m: isize, n: isize) -> isize {
    if m == 0 {
        n + 1
    } else if n == 0 {
        ack1(m - 1, 1)
    } else {
        ack1(m - 1, ack1(m, n - 1))
    }
}

#[ensures="result == ack_pure(m, n)"]
fn ack2(m: isize, n: isize) -> isize {
	match (m, n) {
		(0, n) => n + 1,
		(m, 0) => ack2(m - 1, 1),
		(m, n) => ack2(m - 1, ack2(m, n - 1)),
	}
}

#[trusted]
fn print_isize(a: isize) {
    println!("{}", a); // 125
}

fn main() {
    let a1 = ack1(3, 4);
    let a2 = ack2(3, 4);
    assert!(a1 == a2);
    print_isize(a1);
}
