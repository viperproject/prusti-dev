// This test instantiates two instances of `A` and checks that their models are independent.
use prusti_contracts::*;

struct A(i32);

#[model]
struct A {
    val: i32,
}

#[trusted]
#[ensures( result.model().val == model_val)]
fn create_a(model_val: i32) -> A {
    A{ 0: 0 }
}

#[requires( a.model().val == expected_val )]
fn verify_model(a: A, expected_val: i32) {

}

fn main() {
    let a1 = create_a(4);
    let a2 = create_a(5);
    verify_model(a1, 4);
    verify_model(a2, 5);
}