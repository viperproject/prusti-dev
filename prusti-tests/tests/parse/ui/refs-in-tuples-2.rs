fn cond() -> bool { true }

fn main() {
    let mut x = 0;
    let mut y = 1;

    let xy = (&mut x, &mut y);

    let z = if cond() {
        xy.0
    } else {
        xy.1
    };

    *z = 2;
    assert!(x == 2 || y == 2);
}
