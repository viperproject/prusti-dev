fn rand<T>() -> T { loop {} }
use std::mem::swap;

fn may_swap<T>(mx: &mut T, my: &mut T) {
  if rand() {
    swap(mx, my);
  }
}
fn swap2_dec_three<'a>(
  mmma: &mut &'a mut &'a mut i32, mmmb: &mut &'a mut &'a mut i32, mmmc: &mut &'a mut &'a mut i32,
) {
  may_swap(mmma, mmmb);
  may_swap(mmmb, mmmc);
  may_swap(mmma, mmmb);
  may_swap(*mmma, *mmmb);
  may_swap(*mmmb, *mmmc);
  may_swap(*mmma, *mmmb);
  if rand() {
    return;
  }
  ***mmma -= 1;
  ***mmmb -= 2;
  ***mmmc -= 3;
  swap2_dec_three(mmma, mmmb, mmmc);
}
fn main() {
  let mut a = rand();
  let mut b = rand();
  let mut c = rand();
  let a0 = a;
  swap2_dec_three(&mut &mut &mut a, &mut &mut &mut b, &mut &mut &mut c);
  assert!(a0 >= a && a0 - a <= 3);
}
