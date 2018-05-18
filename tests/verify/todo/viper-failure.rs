extern crate prusti_contracts;

struct A;
struct B(A, A);
struct C(B, B);

fn consume_a(a: A) {}
fn consume_a_ref(a: &A) {}

fn main() {
    let c = C(B(A, A), B(A, A));

    let x = &(c.0).0; // _8

    let y = &(c.0).1; // _9

    consume_a((c.1).0);

    consume_a((c.1).1);

    consume_a_ref(y);

    consume_a_ref(x);
}
