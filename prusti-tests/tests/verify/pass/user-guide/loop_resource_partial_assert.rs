//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

//// ANCHOR: code
obligation! {
    fn ob(amount: usize);
}

#[trusted]
#[ensures(ob(10))]
fn get10() {}

#[trusted]
#[requires(ob(1))]
fn use1() {}

fn main() {
    get10();
    prusti_assert!(ob(10));
    let mut i = 5;
    while i > 0 { 
        body_invariant!(ob(i));
        use1();
        i -= 1;
    }
    prusti_assert!(ob(5));
    use1();
    use1();
    use1();
    use1();
    use1();
}
//// ANCHOR_END: code
