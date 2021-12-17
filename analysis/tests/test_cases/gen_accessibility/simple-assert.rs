fn foo(x: i32, y: i32, guard: bool) {
    let mut z = x + y;

    if guard {
        z = 100;
    }

    // later...

    if guard {
        assert!(z == 100);
    } else {
        assert!(z - x == y);
    }
}

fn main() {
    let x = 10;
    let y = 10;
    debug_assert!(x + y == 20);
}
