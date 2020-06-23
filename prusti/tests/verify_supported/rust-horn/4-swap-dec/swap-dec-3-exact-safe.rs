fn rand<T>() -> T { loop {} }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec_bound<'a>(n: i32, mma: &mut &'a mut i32, mmb: &mut &'a mut i32) {
  may_swap(mma, mmb);
  if n == 0 {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  swap_dec_bound(n - 1, mma, mmb);
}
fn main() {
  let n = rand();
  let mut a = rand();
  let mut b = rand();
  let a0 = a;
  swap_dec_bound(n, &mut &mut a, &mut &mut b);
  assert!(a0 >= a && a0 - a <= 2 * n);
}
