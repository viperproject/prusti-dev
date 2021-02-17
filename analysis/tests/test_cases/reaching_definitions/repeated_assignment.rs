#[analyzer::run]
fn main() {
    let mut x = 1;
    let mut y = 3;
    x = input();
    if x > 2 {
        y = 5;
    }
    else {
        y = 7;
    }
    y = 25;
}

fn input() -> i32 {
    return 42;
}