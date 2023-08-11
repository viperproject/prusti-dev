use prusti_contracts::*;

obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, loc))]
fn alloc(loc: usize) {}

fn main() {
    let mut i = 0;
    loop { //~ ERROR a loop iteration might leak instances of obligation `alloced`
        body_invariant!(alloced(i, 0));
        let zero = 0;
        alloc(zero);
        alloc(zero);
        i += 1;
    }
}
