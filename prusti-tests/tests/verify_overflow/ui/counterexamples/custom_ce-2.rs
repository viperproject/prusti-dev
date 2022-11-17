// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pprint_counterexample_if_model_is_present=true

use prusti_contracts::*;

#[print_counterexample("X: a = {}", a)]
struct X {
    a: i32,
}

#[print_counterexample("model of X: a = {}", a)]
#[model]
struct X {
   a: i32,
}



#[requires(x.model().a == x.a && x.a == 2)] //force specific counterexample
#[ensures(x.model().a == 5)] 
fn test1(x: X) {}

#[requires(x.model().a == x.a && x.a == 2)] //force specific counterexample
#[requires(y.model().a == y.a)]
#[ensures(!(x.model().a == y.model().a))]
fn test2(x: X, y: X) {}

fn main() {}