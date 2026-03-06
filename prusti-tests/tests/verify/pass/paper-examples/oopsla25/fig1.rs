// Figure 1: Ownership and Borrowing
// (a) replace_x_own - ownership transfer
// (b) replace_x - mutable borrowing

struct Pos2D<T> { x: T, y: T }

fn replace_x_own<T>(mut pos: Pos2D<T>,
                    new_x: T) -> Pos2D<T> {
    let old_x = pos.x;
    pos.x = new_x;
    return pos;
}

fn replace_x<T>(pos: &mut Pos2D<T>,
                new_x: T) {
    let x_ref = &mut (*pos).x;
    *x_ref = new_x;
}

fn caller(mut original: Pos2D<i32>) {
    let pos = &mut original;
    replace_x(pos, 0);
}

fn main() {}
