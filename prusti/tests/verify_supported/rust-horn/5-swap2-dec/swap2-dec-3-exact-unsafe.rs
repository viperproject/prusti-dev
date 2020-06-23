fn rand<T>() -> T { loop {} }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap2_dec_bound<'a>(n: i32, mmma: &mut &'a mut &'a mut i32, mmmb: &mut &'a mut &'a mut i32) {
  may_swap(mmma, mmmb);
  may_swap(*mmma, *mmmb);
  if n == 0 {
    return;
  }
  ***mmma -= 1;
  ***mmmb -= 2;
  swap2_dec_bound(n - 1, mmma, mmmb);
}
fn main() {
  let n = rand();
  let mut a = rand();
  let mut b = rand();
  let a0 = a;
  swap2_dec_bound(n, &mut &mut &mut a, &mut &mut &mut b);
  assert!(a0 >= a && a0 - a < 2 * n);
}
