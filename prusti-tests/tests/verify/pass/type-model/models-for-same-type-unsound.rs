// This test instantiates two instances of `A` and checks that their models are independent.
// Notice that `A` has no fields, which introduces a soundness issues.
// The reason for this behavior is that the encoding of `A` (w/o fields) in Viper
// assumes that all instances are equal, i.e. there is no notion of inequality for two `A`s.
// Hence, we cannot refer to different models for different instances of `A`.
// If `A` had fields, the code verifies as expected.
//
// This code will print a warning to a user.

use prusti_contracts::*;

struct A;

#[model]
struct A {
    val: i32,
}

#[trusted]
#[ensures( result.model().val == model_val)]
fn create_a(model_val: i32) -> A {
    A { }
}

#[requires( _a.model().val == _expected_val )]
fn verify_model(_a: A, _expected_val: i32) {

}

fn main() {
    let a1 = create_a(4);
    let a2 = create_a(5);
    verify_model(a1, 42);
    verify_model(a2, 42);
}