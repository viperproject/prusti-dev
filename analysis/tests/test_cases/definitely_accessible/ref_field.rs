fn foo<T>(_x: T) {}

#[analyzer::run]
fn main() {
    let x = (Box::new(123), Box::new(123));
    let y = &x.0;
    let mut z = (y, y, y);
    z.2 = &x.1;
    foo(&z);
    foo(&z);
    drop(x);
}
