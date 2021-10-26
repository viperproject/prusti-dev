
fn main() {
    let a = abs(-1);
    let b = abs(1);
    println!("{}", a+b);
}

#[analyzer::run]
fn abs(x: i32) -> i32 {
    let res: i32;
    if x >= 0 {
        res = x;
    }
    else {
        res = -x;
    }
    return res;
}
