// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

// #[requires(forall(|a: Map<u32,u32>, b: u32| a == 5 ==> b == 10, triggers=[(1+1,), (2,3), (4,)]))]
// #[requires((true ==> true) || true)]
// #[requires(true && true || true)]
// #[requires((true && true) || true ==> forall(|| 1+1) || true && true)]
#[requires(true ==> true)]
fn test1() {}

// #[ensures((1+1 == 2) && ((1 + 1) == 2))]
// fn test2() {}
//
// fn test3() {
//     for _ in 0..2 {
//         invariant!(true)
//     }
// }
//
// #[requires(true)]
// #[ensures(true)]
// fn test4() {
//     for _ in 0..2 {
//         invariant!(true)
//     }
// }

fn main() {}
