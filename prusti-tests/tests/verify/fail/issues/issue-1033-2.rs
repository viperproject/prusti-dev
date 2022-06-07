use prusti_contracts::*;

fn main() {}

pub struct Foo<T>(T);

impl<T: PartialEq> Foo<T> {
    #[pure]
    #[ensures(result == (left == right))]
    fn eq(left: T, right: T) -> bool { //~ ERROR pure function parameters must be Copy
        left == right
    }
}
