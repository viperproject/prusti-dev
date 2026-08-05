fn main() {
    let a = 10;
    let b = (a + 2) - 6;  // 6
    let c = (b - 1) * 2;  // 10
    let d = -c;  // -10
    let x = (0 < d) || (d > 10);  // true
    let y = (10 >= d) && (d <= 0);  // false
    let z = (a == b) || (x != y); // true
    assert!(d == -10 && z);

    assert!(9 / 2 == 4);
}

// Compound assignments on primitives lower to a same-place form, e.g.
// `x /= y` to `x = Div(copy x, move y)`: the destination is also an operand,
// so its snapshot must be read before the assignment exhales its predicate.

fn compound_assign(x: i32, y: i32) -> i32 {
    let mut x = x;
    if y != 0 {
        x /= y;
        x %= 7;
    }
    x
}

fn compound_assign_field(t: (i32, i32)) -> (i32, i32) {
    let mut t = t;
    if t.1 != 0 {
        t.0 /= t.1;
    }
    t
}
