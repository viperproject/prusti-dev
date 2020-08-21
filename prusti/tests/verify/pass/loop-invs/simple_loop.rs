// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

fn main() {
    let mut i = 10;
    while i > 0 {
        body_invariant!(i <= 10);
        i -= 1;
    }
}
