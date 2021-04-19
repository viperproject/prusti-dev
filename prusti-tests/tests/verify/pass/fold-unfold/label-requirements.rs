use prusti_contracts::*;

enum MyOption {
    Some(i32),
}

#[pure]
fn is_some(opt: &MyOption) -> bool {
    matches!(opt, MyOption::Some(_))
}

#[ensures(old(is_some(&opt)) ==> is_some(&result))]
fn inc(opt: MyOption) -> MyOption {
    MyOption::Some(0)
}

fn test() {
    inc(MyOption::Some(5));
}

fn main() {}
