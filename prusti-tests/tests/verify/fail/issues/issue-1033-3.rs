use prusti_contracts::*;

fn main() {}

pub struct Foo<T>(T);

impl<T: PartialEq> Foo<T> {
    #[ensures(result == (left == right))]
    fn eq(left: T, right: T) -> bool {
        left == right
    }
}

#[pure]
pub fn test() {
    assert!(Foo::eq(0, 0)); //~ ERROR use of impure function
}
