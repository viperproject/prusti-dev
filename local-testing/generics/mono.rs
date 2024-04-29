use prusti_contracts::*;

struct Pair<X, Y>(X, Y);

#[pure]
#[trusted]
fn f<T, U>(t: T, u: U) -> T {
    t
}

#[pure]
fn g<U, V, W>(x: Pair<U, V>, w: W) -> Pair<U, V> {
   f(x, w)
}

fn main(){
    f(Pair(1, 2), 3);
    g(Pair(4, 5), 6);
}
