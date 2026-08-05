fn main() {
    let n = 1;
    let x = match n {
        -1 => 123,
        0 => -1,
        1 => 1,
        2 => 42,
        _ => unreachable!()
    };
}

// A `match` with a literal in an aggregate field makes MIR switch on the
// field place directly (e.g. `switchInt(copy (_3.0))`), so the discriminant
// must be read before the PCG re-packs the aggregate for the CFG join.

struct Point {
    x: i32,
    y: i32,
}

fn tuple_literal(m: i32, n: i32) -> i32 {
    match (m, n) {
        (0, n) => n,
        (m, _) => m,
    }
}

fn struct_literal(p: Point) -> i32 {
    match p {
        Point { x: 0, y } => y,
        Point { x, .. } => x,
    }
}

fn nested_literal(t: ((i32, i32), i32)) -> i32 {
    match t {
        ((0, x), _) => x,
        ((x, _), _) => x,
    }
}

fn multiple_literals(t: (i32, i32)) -> i32 {
    match t {
        (0, 0) => 0,
        (0, y) => y,
        (x, 0) => x,
        (x, y) => x + y,
    }
}
