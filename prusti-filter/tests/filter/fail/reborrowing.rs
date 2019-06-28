fn take(_x: &mut Box<i32>) {}

fn main() {
    let mut x = Box::new(123);
    let mut y = &mut x;

    loop {
        y = &mut x;
        take(y);
    }
}
