use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[pure] // <=== Error triggered by this
    #[requires(self.is_some())]
    #[ensures(old(self) === Some(result))]
    pub fn unwrap(self) -> T; //~ ERROR old expressions should not appear in the postconditions of pure functions

    #[pure]
    #[ensures(result == matches!(self, Some(_)))]
    pub const fn is_some(&self) -> bool;
}

#[pure]
#[requires(x.is_some())]
fn test(x: Option<i32>) -> i32 {
    // Following error is due to stub encoding of invalid external spec for function `unwrap()`
    x.unwrap() //~ ERROR precondition of pure function call might not hold
}

fn main() { }
