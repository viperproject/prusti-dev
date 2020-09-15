use prusti_contracts::*;

struct Number<S, T> {
    i: i32,
    s: S,
    t: T,
}

#[requires(arg.i >= 9000)]
#[ensures(arg.i >= old(arg.i) - 1000)]
fn test1<A, B>(arg: &mut Number<A, B>) {
    arg.i -= 1000;
}

#[requires(arg.i >= 9000)]
#[ensures(arg.i >= 8000)]
fn test2<A, B>(arg: &mut Number<B, A>) {
    test1(arg);
}

fn main() {}
