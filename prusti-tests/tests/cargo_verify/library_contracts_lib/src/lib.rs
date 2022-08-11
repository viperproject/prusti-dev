use prusti_contracts::*;

pub enum Opt<T> {
    Some(T),
    None
}

impl<T> Opt<T> {
    // TODO fix the error related to pure functions
    #[pure]
    // #[ensures(matches!(*self, Opt::Some(..)) == result)]
    pub fn is_some(&self) -> bool {
        matches!(*self, Opt::Some(..))
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
