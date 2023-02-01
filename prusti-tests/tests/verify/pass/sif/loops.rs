// compile-flags: -Psif=true

use prusti_contracts::*;

#[requires(forall(|i: usize| 0 <= i && i < ts.len() ==> low(ts[i])))]
#[ensures(low(result))]
fn sum_array_low(ts: &[i32]) -> i32 {
    let mut i = 0;
    let mut res = 0;

    while i < ts.len() {
        res += ts[i];
        i += 1;
    }

    res
}

#[ensures(forall(|i: usize| 0 <= i && i < ts.len() ==> low(ts[i])) ==> low(result))]
fn sum_array(ts: &[i32]) -> i32 {
    let mut i = 0;
    let mut res = 0;

    while i < ts.len() {
        res += ts[i];
        i += 1;
    }

    res
}

#[ensures(low(result))]
fn produce_low() -> i32 {
    42
}

#[ensures(forall(|i: usize| 0 <= i && i < array.len() ==> low(array[i])))]
fn fill_with_low(array: &mut [i32]) {
    let mut i = 0;
    while i < array.len() {
        array[i] = produce_low();
        i += 1;
    }
}

fn main() {
    let mut low_array = [1, 2, 3, 4, 5];
    fill_with_low(&mut low_array);

    let res1 = sum_array_low(&low_array);
    prusti_assert!(low(res1));

    let res2 = sum_array(&low_array);
    prusti_assert!(low(res2));
}
