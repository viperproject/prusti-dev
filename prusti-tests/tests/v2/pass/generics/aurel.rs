use prusti_contracts::*;

#[pure] fn id<T>(a: T) -> T { a }
#[pure] fn test1() -> i32 { id(42) }
#[pure] fn test2() -> bool { id(true) }

#[ensures(test1() == 42)]
#[ensures(test2())]
fn main() {}
