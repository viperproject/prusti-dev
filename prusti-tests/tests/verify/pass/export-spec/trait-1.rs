extern crate prusti_contracts;
use prusti_contracts::*;

struct Foo<T>(T);

#[export_spec(::)]
impl<T> Foo<T> {
    #[pure]
    #[ensures(result == self.0)]
    pub fn bar(self) -> T { self.0 }
}


fn main() {}