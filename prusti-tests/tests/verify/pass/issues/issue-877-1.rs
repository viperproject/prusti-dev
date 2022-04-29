use prusti_contracts::*;

fn main() {}

#[ensures(result <= 3)]
fn foo() -> usize {
    let mut a = [1, 2, 3];
    let mut i = 0;
    while i < 3 {
        body_invariant!(i < 3);
        body_invariant!(forall(|j: usize| (0 <= j && j < i) ==> (a[j] <= j + 2),triggers=[(a[j],)]));
        body_invariant!(forall(|j: usize| (i <= j && j < 3) ==> (a[j] <= j + 1),triggers=[(a[j],)]));
        body_invariant!(a[i] <= i + 1);
        let tmp = a[i] + 1;
        a[i] = tmp;
        i += 1;
    }
    a[1]
}

#[ensures(result <= 3)]
fn bar() -> usize {
    let mut a = [1, 2, 3];
    let mut i= 0;
    while i < 3 {
        body_invariant!(i < 3);
        body_invariant!(forall(|j: usize| (0 <= j && j < i) ==> (a[j] <= j + 2),triggers=[(a[j],)]));
        body_invariant!(forall(|j: usize| (i <= j && j < 3) ==> (a[j] <= j + 1),triggers=[(a[j],)]));
        body_invariant!(a[i] <= i + 1);
        let tmp = a[i] + 1;
        set(&mut a, i, tmp);
        i += 1;
    }
    a[1]
}

#[requires(0 <= i && i < 3)]
#[ensures(forall(|j: usize| (0 <= j && j < 3 && j != old(i)) ==> (a[j] == old(a[j])), triggers=[(a[j],)]))]
#[ensures(a[old(i)] == old(v))]
fn set(a: &mut [usize; 3], i: usize, v: usize) {
    a[i] = v;
}
