// This struct can not be copied or cloned
struct T;

enum Either {
    Left(T),
    Right,
}

enum OptionEither {
    Some(Either),
}

fn test(x: OptionEither) {
    // In this particular situation the match does not move out values from the enumeration
    let y = match x {
        OptionEither::Some(Either::Left(_)) => true,
        OptionEither::Some(Either::Right) => false,
    };
    let z = match x {
        OptionEither::Some(Either::Left(_)) => true,
        OptionEither::Some(Either::Right) => false,
    };
    assert!(y == z);
}

fn main() {}
