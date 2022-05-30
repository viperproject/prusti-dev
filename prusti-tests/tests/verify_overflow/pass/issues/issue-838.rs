fn foo(x: &i32) -> &i32 {
    x
}
fn main() {
    let x = 5;
    let y: &i32 = foo(&x);
}
