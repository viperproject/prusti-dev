// Regression test: parametric const encoding used arg position instead of
// p.index, causing a crash when type params appear before the const param.
use prusti_contracts::*;

#[trusted] fn first_tn<T: Copy, const N: usize>(arr: [T; N]) -> T { arr[0] }
#[trusted] fn first_nt<const N: usize, T: Copy>(arr: [T; N]) -> T { arr[0] }
#[trusted] fn first_n<const N: usize>(arr: [i32; N]) -> i32 { arr[0] }
#[trusted] fn first_ttn<T: Copy, U: Copy, const N: usize>(a: [T; N], b: [U; N]) -> (T, U) { (a[0], b[0]) }

fn main() {
    let _ = first_tn::<i32, 3>([1, 2, 3]);
    let _ = first_nt::<3, i32>([1, 2, 3]);
    let _ = first_n::<3>([1, 2, 3]);
    let _ = first_ttn::<i32, bool, 2>([1, 2], [true, false]);
}
