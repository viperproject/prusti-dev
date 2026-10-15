use prusti_contracts::*;

trait Src { type Out; }
struct S;
impl Src for S { type Out = u32; }

struct Wrap<T>(T);

trait Get {
    type Item;
    #[ensures(result)]
    fn take(&self, x: Self::Item) -> bool;
}

struct W<I>(I);

// `T` is only reachable through the where-clause, and the trait method's
// argument type `Self::Item` normalizes to the concrete `Wrap<T>`.
impl<I, T> Get for W<I> where I: Src<Out = T> {
    type Item = Wrap<T>;
    fn take(&self, _x: Wrap<T>) -> bool { true }
}

fn use_get<G: Get>(g: &G, x: G::Item) -> bool {
    g.take(x)
}

fn main() {
    let w = W(S);
    let _ = use_get(&w, Wrap(5));
}
