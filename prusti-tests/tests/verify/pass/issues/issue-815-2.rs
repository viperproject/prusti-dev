use prusti_contracts::*;

#[pure]
#[requires(0 <= i && i < 10)]
const fn get(a: &[i32; 10], i: usize) -> i32 {
    a[i]
}

#[requires(0 <= i && i < 10)]
#[ensures(forall(|j: usize|
    (0 <= j && j < 10 && j != old(i)) ==> (get(a, j) == old(get(a, j))),
    triggers=[(get(a, j),)]
))]
#[ensures(get(a, i) == old(v))]
fn set(a: &mut [i32; 10], i: usize, v: i32)  {
    a[i] = v;
}

fn main() {}
