extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
impl<T> Option<T> {
    #[ensures(matches!(*self, Some(_)) == result)]
    fn is_some(&self) -> bool;
}
