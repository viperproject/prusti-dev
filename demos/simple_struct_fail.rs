use prusti_contracts::*;

#[derive(Clone, Copy)]
struct Loc {
    cluster: usize,
    slot: usize,
}

obligation! {
    fn alloced(amount: usize, loc: Loc);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: Loc) {
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: Loc) {
}

#[ensures(alloced(1, loc))]
#[requires(alloced(1, loc))]
fn operate_on(loc: Loc) {
}

// << there should be #[pure] or a specification here
fn get_loc(slot: usize) -> Loc {
    Loc { cluster: 33, slot }
}

fn main() {
    let l = Loc { cluster: 33, slot: 90 };
    alloc(l);
    operate_on(Loc { cluster: 33, slot: 90 });

    // error here: exhale might fail (of the precondition of dealloc)
    dealloc(get_loc(80 + 10));
}

// DOES NOT VERIFY
