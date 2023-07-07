use prusti_contracts::*;

obligation! {
    fn obl(amount: usize, x: usize);
}

#[trusted]
#[ensures(forall(|x: usize| obl(1, x)))]
fn alloc1() {}

#[ensures(forall(|x: usize| obl(1, x)))]
fn client1() {
    alloc1()
}

#[trusted]
#[ensures(forall(|x: usize| (x % 2 == 0) ==> obl(1, x)))]
fn alloc2() {}

#[ensures(forall(|x: usize| (x % 2 == 0) ==> obl(1, x)))]
fn client2() {
    alloc2()
}

#[pure]
fn pred(x: usize) -> bool {
    x > 15 && x % 3 == 0
}

#[trusted]
#[ensures(forall(|x: usize| pred(x) ==> obl(1, x)))]
fn alloc3() {}

#[ensures(forall(|x: usize| pred(x) ==> obl(1, x)))]
fn client3() {
    alloc3()
}

#[trusted]
#[ensures(forall(|x: usize| obl(33, x) & obl(42, x)))]
fn alloc4() {}

#[ensures(forall(|x: usize| obl(33, x) & obl(42, x)))]
fn client4() {
    alloc4()
}

#[trusted]
#[ensures(forall(|x: usize| if x % 8 < 4 { obl(33, x) } else { obl(42, x) }))]
fn alloc5() {}

#[ensures(forall(|x: usize| if x % 8 < 4 { obl(33, x) } else { obl(42, x) }))]
fn client5() {
    alloc5()
}

#[trusted]
#[ensures(forall(|x: usize| (16 <= x && x < 256 || x % 5 == 0 && x < 512) ==> obl(1, x)))]
fn alloc6() {}

#[ensures(forall(|x: usize| (16 <= x && x < 256 || x % 5 == 0 && x < 512) ==> obl(1, x)))]
fn client6() {
    alloc6()
}


// the following test checks that non-trivial injectivity of quantified resources can be proved

#[trusted]
#[ensures(forall(|x: usize| (x % 5 == 3) ==> obl(1, x / 2)))]
fn alloc7() {}

#[ensures(forall(|x: usize| (x % 5 == 3) ==> obl(1, x / 2)))]
fn client7() {
    alloc7()
}

fn main() {}
