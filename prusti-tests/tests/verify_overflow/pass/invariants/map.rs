// compile-flags: -Penable_type_invariants=true
use std::collections::BTreeSet;

// No invariants are used here, but the encoding of the `union` operation
// introduces datatypes that only vary in a generic lifetime parameter. For the
// purpose of type invariants, these datatypes should be treated as the same
// datatype.
fn union(lhs: &BTreeSet<u32>) {
    lhs.union(lhs).cloned();
}

fn main() {}
