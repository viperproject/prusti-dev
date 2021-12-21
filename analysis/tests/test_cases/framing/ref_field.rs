fn foo<T>(_x: T) {}

#[analyzer::run]
fn main() {
    let mut x = (Box::new(123), Box::new(123));
    foo(&x.0);
    foo(&mut x.1);
    drop(x);
}
