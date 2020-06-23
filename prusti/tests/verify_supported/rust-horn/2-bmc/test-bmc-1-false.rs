fn rand<T>() -> T { loop {} }

fn main() {
  let mut x = 1;
  let mut y = 1;
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  if rand() {
    x += 1;
    y += 1;
  }
  assert!(x <= 10);
}
