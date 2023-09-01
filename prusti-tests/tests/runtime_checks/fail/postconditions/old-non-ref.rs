//@run: 101
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

#[derive(Clone)]
struct Something {
    pub field: i32,
}

// has to fail, since x.field in specification refers
// to old state too
#[trusted]
#[insert_runtime_check]
#[ensures(old(x.field) + 4 == x.field)]
fn nonsense(mut x: Something) {
    x.field = x.field + 4;
}

fn main() {
    let s = Something {
        field: 1,
    };
    nonsense(s);
}
