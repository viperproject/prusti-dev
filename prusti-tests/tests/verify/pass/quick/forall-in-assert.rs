// A quantifier closure inside an assertion's closure: encoding the nested
// closure's type must name it after its nearest non-closure ancestor
// (`item_name` on a closure DefId ICEs in the compiler).

use prusti_contracts::*;

fn forall_in_assert() {
    prusti_assert!(forall(|i: i64| i == i));
}

fn main() {}
