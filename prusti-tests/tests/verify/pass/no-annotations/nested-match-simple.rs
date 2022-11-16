enum Either {
    Left,
    Right,
}

enum OptionEither {
    Some(Either),
    None,
}

fn none_or_left(x: OptionEither) -> bool {
    match x {
        OptionEither::None => true,
        OptionEither::Some(Either::Left) => true,
        OptionEither::Some(Either::Right) => false,
    }
    // Here we had an issue with the first implementation of enumerations for the fold/unfold:
    // 1. The `OptionEither::None` branch has a `Either(x.enum_0_0)` predicate.
    // 2. The `OptionEither::Some(_)` branches has a `int(x.enum_0_0.discriminant)` predicate.
    // 3. At join point, the `OptionEither::None` branch tries to unfold `Either(x.enum_1_0)`
    //    to reach the predicate `int(x.enum_1_0.discriminant)` on which the branches seem to agree.
}

fn main() {}
