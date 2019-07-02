fn take(_x: &mut Box<i32>) {}

fn main() {
    let mut x = Box::new(123);
    let mut y = &mut x;

    while true {
        y = &mut x; //~ ERROR reborrow
        take(y);
    }
}
