#[analyzer::run]
fn main() {
    let a = f(-1);
    let b = f(1);

    let c = a + b;
    let d = f(c);
}

fn f(x: i32) -> i32 {
    return x;
}