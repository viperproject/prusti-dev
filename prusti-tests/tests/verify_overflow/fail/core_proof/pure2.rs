// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=20 -Psmt_qi_bound_global_kind=100 -Pverify_specifications_backend=silicon
//
// This test is executed only with Silicon because we have a matching
// loop that gets triggered by Carbon.

use prusti_contracts::*;

#[pure]
#[requires(n >= 0)]
#[ensures(result <= n)]
#[terminates(Int::new_usize(n))]
fn count(n: usize) -> usize {
    if n == 0 { 0 }
    else { count(n-1) + 1 }
}

// This is expected to fail because the gas is set to 2 and proving this
// requires unfolding 3 times. If this succeeded, then it would indicate
// that we have a matching loop.
#[ensures(count(3) == 3)] //~ ERROR postcondition might not hold.
fn test6() {}

fn main() {}
