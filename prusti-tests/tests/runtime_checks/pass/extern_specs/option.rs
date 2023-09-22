//@run
use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[pure]
    #[insert_runtime_check]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[insert_runtime_check]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[trusted]
    #[insert_runtime_check]
    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[trusted]
fn main() {
    let x = Some(5);
    x.unwrap();
}
