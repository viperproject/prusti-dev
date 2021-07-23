use prusti_contracts::*;

pub fn test<T>(x: &'static T) -> &'_ T {
    &*x
}

fn main() {
}
