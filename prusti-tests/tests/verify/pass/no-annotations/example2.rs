#[derive(Copy, Clone)]
enum MyOption {
    Some((i32, i64)),
    None
}

fn foo(x: ((i32, MyOption), bool)) -> ((i32, MyOption), bool) {
    let y = x;
    let z = x;
    y
}

fn main() {

}
