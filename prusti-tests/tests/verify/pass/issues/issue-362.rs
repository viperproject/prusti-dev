use prusti_contracts::*;

enum MyOption {
    None,
    Some(i32),
}

impl MyOption {
    #[pure]
    fn is_some(&self) -> bool { matches!(self, MyOption::Some(_)) }

    #[requires(
        self.is_some() ==>
            5 == match self {
                MyOption::Some(n) => n,
                MyOption::None => unreachable!(),
            }
    )]
    #[trusted]
    fn map(self) -> MyOption { unimplemented!() }
}

fn test() {
    MyOption::None.map();
}

fn main() {}
