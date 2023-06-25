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
fn alloc(loc: Loc) {}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: Loc) {}

#[pure]
#[ensures(result.cluster == 0 && result.slot == 0)]
fn get_loc_zero() -> Loc {
    Loc { cluster: 0, slot: 0 }
}

#[ensures(cluster == 0 ==> alloced(1, get_loc_zero()))]
#[ensures(cluster != 0 ==> alloced(1, Loc { cluster, slot: 0 }))]
fn alloc_first(cluster: usize) {
    alloc(Loc { cluster, slot: 0 })
}

fn main() {}
