// Coverage for ghost (`Int`/`Real`) values in impure, executable code: they
// can be bound to locals, combined with operators, passed and returned, and
// related in contracts. `===` (snapshot equality) is exercised throughout.

use prusti_contracts::*;

// Ghost `Int` values built and combined in executable (non-spec) code, with a
// postcondition relating the result to the arguments.
#[ensures(result === Int::from(a) + Int::from(b))]
fn int_sum(a: i64, b: i64) -> Int {
    let x = Int::from(a);
    let y = Int::from(b);
    x + y
}

// Executable code threading a ghost through several statements.
#[ensures(result === Int::from(6))]
fn int_pipeline() -> Int {
    let a = Int::from(1);
    let b = a + Int::from(2);
    let c = b * Int::from(2);
    c
}

// Ghost `Real` in executable code.
#[ensures(result === Real::from(2.0) * Real::from(x))]
fn real_double(x: f64) -> Real {
    let r = Real::from(x);
    r + r
}

fn client() {
    // The postconditions flow the ghost values back to the caller.
    let s = int_sum(2, 3);
    prusti_assert!(s === Int::from(5));

    let p = int_pipeline();
    prusti_assert!(p === Int::from(6));

    // Snapshot equality (`===`) relating two ghost locals directly.
    prusti_assert!(s + Int::from(1) === p);
}

// Ghost code uses the *checked* native collection operations: in-bounds
// indexing, updates and lookups verify.
fn ghost_collections() {
    ghost! {
        let s = seq![1, 2, 3];
        let _x = s[Int::from(1)];
        let _s2 = s.update(Int::from(0), 4);
        let _s3 = s[Int::from(1)..Int::from(3)];
        let _s4 = s[..Int::from(2)];
        let m = map![1 => 10];
        let _v = m[1];
        let _m2 = m.setminus(set![1]);
        // `Clone` is a shared (non-spec-only) operation.
        let _s5 = s.clone();
    };
}
