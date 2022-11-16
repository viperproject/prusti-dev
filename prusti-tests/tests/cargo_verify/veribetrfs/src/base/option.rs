use prusti_contracts::*;

pub enum Opt<T> {
    None,
    Some(T),
}

use Opt::*;

impl<T> Opt<T> {
    #[pure]
    pub fn is_none(&self) -> bool {
        match self {
            None => true,
            _ => false,
        }
    }

    #[pure]
    pub fn is_some(&self) -> bool {
        !self.is_none()
    }

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T {
        match self {
            Some(t) => t,
            None => panic!("called unwrap on `None` instance."),
        }
    }

    #[ensures(result.is_some())]
    pub fn wrap(t: T) -> Self {
        Some(t)
    }
}
