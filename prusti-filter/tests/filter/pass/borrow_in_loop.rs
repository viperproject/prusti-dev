fn take(_x: &mut Box<i32>) {}

fn main() {
    let mut x = Box::new(123);
    loop {
        let y = &mut x;
        take(y);
    }
}
