// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

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

fn main(val: i32){
    let a = create_a(val);
    verify_model(a, val);
}