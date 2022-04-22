use prusti_contracts::*;

#[extern_spec]
impl<T: PartialEq> std::option::Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() == ! result)]
    #[ensures(matches!(*self, None) == result)]
    pub fn is_none(&self) -> bool;
}

trait OptionPeeker<T> {
    #[pure]
    fn peek(&self) -> T;
}

#[refine_trait_spec]
impl<T: Copy> OptionPeeker<T> for Option<T> {
    #[pure]
    #[requires(self.is_some())]
    fn peek(&self) -> T {
        match self {
            Some(v) => *v,
            None => unreachable!(),
        }
    }
}

fn main() {
    let o = Some(5);
    assert!(o.peek() == 5);
}