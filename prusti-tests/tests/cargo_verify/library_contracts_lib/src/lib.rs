extern crate prusti_contracts;
use prusti_contracts::*;

pub enum Opt<T> {
    OSome(T),
    ONone
}

impl<T> Opt<T> {
    #[ensures(matches!(*self, Opt::OSome(_)) == result)]
    pub fn is_some(&self) -> bool {
        match self {
            Opt::OSome(_) => true,
            Opt::ONone => false
        }
    }
}
