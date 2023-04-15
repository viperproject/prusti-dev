// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

// #[requires(low(ts))]
// #[ensures(low(result))]
// fn sum_array_low(ts: &[i32]) -> i32 {
//     let mut i = 0;
//     let mut res = 0;

//     while i < ts.len() {
//         body_invariant!(low(i));
//         body_invariant!(low(res));
//         res += ts[i];
//         i += 1;
//     }

//     res
// }

// #[requires(forall(|i: usize| low(ts[i])))]
// #[ensures(low(result))]
// fn sum_array_low2(ts: &[i32]) -> i32 {
//     let mut i = 0;
//     let mut res = 0;

//     while i < ts.len() {
//         body_invariant!(low(i));
//         body_invariant!(low(res));
//         res += ts[i];
//         i += 1;
//     }

//     res
// }

// #[ensures(low(ts) ==> low(result))]
// fn sum_array(ts: &[i32]) -> i32 {
//     let mut i = 0;
//     let mut res = 0;

//     while i < ts.len() {
//         body_invariant!(low(i));
//         body_invariant!(low(ts) ==> low(res));
//         res += ts[i];
//         i += 1;
//     }

//     res
// }

#[trusted]
#[ensures(low(result))]
fn produce_low() -> i32 {
    todo!()
}

// #[requires(0 <= i && i < array.len())]
// #[ensures(low(array[i]))]
// fn replace_low(array: &mut [i32], i: usize) {
//     array[i] = produce_low();
// }

#[requires(low(array.len()))]
#[ensures(forall(|i: usize| i < array.len() ==> low(array[i])))]
fn fill_with_low(array: &mut [i32]) {
    let mut i = 0;
    while i < array.len() {
        body_invariant!(low(i));
        body_invariant!(forall(|j: usize| 0 <= j && j < i ==> low(array[j])));
        array[i] = produce_low();
        // replace_low(array, i);
        i += 1;
    }
}

fn main() {
    // let mut low_array = [1, 2, 3, 4, 5];
    // fill_with_low(&mut low_array);

    // let res1 = sum_array_low(&low_array);
    // prusti_assert!(low(res1));

    // let res2 = sum_array(&low_array);
    // prusti_assert!(low(res2));
}
