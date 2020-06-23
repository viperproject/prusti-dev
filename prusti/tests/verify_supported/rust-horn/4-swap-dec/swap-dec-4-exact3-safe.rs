fn rand<T>() -> T { loop {} }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec_bound_three<'a>(
  n: i32, mma: &mut &'a mut i32, mmb: &mut &'a mut i32, mmc: &mut &'a mut i32,
) {
  may_swap(mma, mmb);
  may_swap(mmb, mmc);
  may_swap(mma, mmb);
  if n == 0 {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  **mmc -= 3;
  swap_dec_bound_three(n - 1, mma, mmb, mmc);
}
fn main() {
  let n = rand();
  let mut a = rand();
  let mut b = rand();
  let mut c = rand();
  let a0 = a;
  swap_dec_bound_three(n, &mut &mut a, &mut &mut b, &mut &mut c);
  assert!(a0 >= a && a0 - a <= 3 * n);
}
