use prusti_contracts::*;
use library_contracts_lib::*;

#[extern_spec]
impl<T> Opt<T> {
    #[ensures(self.is_some() == result.is_some())]
    pub fn map<U, F>(self, f: F) -> Opt<U>
    where
        F: FnOnce(T) -> U;
}
