//@run
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

#[derive(Clone)]
struct Something {
    pub field: i32,
}

// even though x.field is modified, since it not a reference
// if it occurrs in specifications it will be evaluated in
// its old state anyways
#[insert_runtime_check]
#[ensures(old(x.field) == x.field)]
fn nonsense(mut x: Something) {
    x.field = x.field + 4;
}

fn main() {
    let s = Something {
        field: 1,
    };
    nonsense(s);
}
