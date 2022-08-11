extern crate prusti_contracts;
use prusti_contracts::*;

pub enum Opt<T> {
    Some(T),
    None
}

impl<T> Opt<T> {
    // TODO fix the error related to pure functions
    //#[pure]
    #[ensures(matches!(*self, Opt::Some(_)) == result)]
    pub fn is_some(&self) -> bool {
        match self {
            Opt::Some(_) => true,
            Opt::None => false
        }
    }

    pub fn map<U, F>(self, f: F) -> Opt<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Opt::Some(x) => Opt::Some(f(x)),
            Opt::None => Opt::None,
        }
    }
}
