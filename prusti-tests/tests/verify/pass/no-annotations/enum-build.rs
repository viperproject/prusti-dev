enum Enum {
    One(i32),
    Two(i32),
    Three(i32),
}

fn random() -> bool {
    true
}

fn test() -> Enum {
    if random() {
        Enum::One(111)
    } else {
        Enum::Two(222)
    }
    // At the join point we don't have `Enum::Three(i32)`
}

fn main() {}
