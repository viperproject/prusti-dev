// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

/// Failure case for closure macro parsing: missing argument type.

use prusti_contracts::*;

fn main() {
    // TODO: the error is reported with an indicator next to `i` below, but the
    // error is not very clear overall.
    let f = closure!(
        requires(i >= 0),
        ensures(result == i + 1),
        |i| -> i32 { i + 1 }
    );
}
