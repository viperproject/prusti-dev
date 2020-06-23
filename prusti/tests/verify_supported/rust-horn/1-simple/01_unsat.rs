fn rand<T>() -> T { loop {} }

fn main() {
  let mut x = 1;
  let mut y = 1;
  while rand() {
    let t1 = x;
    let t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  assert!(y >= 1);
}
