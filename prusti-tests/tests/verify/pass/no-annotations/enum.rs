enum Either {
    Left(i32),
    Right(i32),
}

fn to_right(x: Either, y: Either) -> Either {
    match x {
        Either::Left(val) |
        Either::Right(val) => {
            Either::Right(val)
        }
    }
}

fn main() {}
