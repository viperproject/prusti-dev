use prusti_contracts::*;

trait OptionPeeker<T> {
    #[pure]
    #[requires(false)]
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
