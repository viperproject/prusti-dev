use prusti_contracts::*;

#[derive(Clone, Copy)]
struct MyWrapper(u32);

impl MyWrapper {
    #[pure]
    #[ensures(self === MyWrapper(result))]
    fn unwrap(self) -> u32 {
        self.0
    }
}

fn test(x: MyWrapper) -> u32 {
    x.unwrap()
}

fn main() { }
