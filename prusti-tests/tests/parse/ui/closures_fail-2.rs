// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(stmt_expr_attributes)]

/// Failure case for closure macro parsing: missing return type.

use prusti_contracts::*;

fn main() {
    let f = closure!(
        requires(i >= 0),
        ensures(result == i + 1),
        |i: i32| i + 1
    );
}
