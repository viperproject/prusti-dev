// Figure 3: Function Calls (max and dec_max_alt)

struct Pos2D<T> { x: T, y: T }

fn max<'a, 'b, 'r>(rx: &'a mut i32,
                   ry: &'b mut i32)
    -> &'r mut i32
where 'a: 'r, 'b: 'r
{
    if *rx > *ry { &mut *rx } else { &mut *ry }
}

fn dec_max_alt<'a>(pos: &'a mut Pos2D<i32>) {
    let rx = &mut pos.x;
    let ry = &mut pos.y;
    let res = max(rx, ry);
    *res -= 1;
}

fn main() {}
