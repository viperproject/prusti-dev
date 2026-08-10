use prusti_contracts::*;

#[extern_spec]
impl<T> std::option::Option<T> {
    #[trusted]
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[trusted]
    #[pure]
    #[ensures(self.is_some() == !result)]
    pub fn is_none(&self) -> bool;

    #[trusted]
    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;

    #[trusted]
    pub fn unwrap_or(self, default: T) -> T;

    #[trusted]
    pub fn unwrap_or_else<F>(self, f: F) -> T
        where F: FnOnce() -> T;

    #[trusted]
    #[requires(self.is_some())]
    pub fn expect(self, msg: &str) -> T;

    #[trusted]
    pub fn as_ref(&self) -> Option<&T>;

    #[trusted]
    pub fn as_mut(&mut self) -> Option<&mut T>;
}

fn main() {
    let mut x = Some(3);
    assert!(x.is_some());
    x = None;
    assert!(x.is_none());
}
