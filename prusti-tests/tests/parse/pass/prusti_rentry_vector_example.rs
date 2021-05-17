use prusti_contracts::*;

// ignore-test: prusti-expr! not yet implemented
#[ensures(result == prusti_expr!(forall(|i: usize| i < self.len() ==> f(x[i]))))]
fn all_of(x: &Vec<u32>, f: fn (u32) -> bool) -> bool {
    for i in x {
        if !f(*i) {
            return false;
        }
    }
    true
}