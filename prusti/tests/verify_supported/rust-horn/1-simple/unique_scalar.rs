fn rand<T>() -> T { loop {} }

fn main() {
  let mut x = 0;
  let mut y = 0;
  let p = if rand() { &mut x } else { &mut y };
  *p = 1;
  x += 1;
  assert!(x < 2);
}
