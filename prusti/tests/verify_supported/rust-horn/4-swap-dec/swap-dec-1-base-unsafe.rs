fn rand<T>() -> T { loop {} }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap_dec<'a>(mma: &mut &'a mut i32, mmb: &mut &'a mut i32) {
  may_swap(mma, mmb);
  if rand() {
    return;
  }
  **mma -= 1;
  **mmb -= 2;
  swap_dec(mma, mmb);
}
fn main() {
  let mut a = rand();
  let mut b = rand();
  let a0 = a;
  swap_dec(&mut &mut a, &mut &mut b);
  assert!(a0 >= a && a0 - a <= 3);
}
