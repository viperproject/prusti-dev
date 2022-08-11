extern crate prusti_contracts;
extern crate library_contracts_lib;
use prusti_contracts::*;
use library_contracts_lib::*;

#[extern_spec]
impl<T> Opt<T> {
    // TODO make the precondition work with external pure function
    //#[ensures(self.is_some() == result.is_some())]
    #[ensures(matches!(self, Opt::Some(_)) == matches!(result, Opt::Some(_)))]
    pub fn map<U, F>(self, f: F) -> Opt<U>
    where
        F: FnOnce(T) -> U;
}
