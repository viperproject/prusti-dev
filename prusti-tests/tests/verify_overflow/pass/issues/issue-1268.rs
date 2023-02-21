use prusti_contracts::*;

enum TestEnum {
    Nil,
}

#[ensures(TestEnum::Nil === TestEnum::Nil)]
fn test() {}

fn main() {
    let foo = 5;
    prusti_assert!(foo === 5);
}
