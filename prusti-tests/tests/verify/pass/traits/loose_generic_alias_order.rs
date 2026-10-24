use prusti_contracts::*;

trait A { type X; }
trait B { type Y; }
trait C { type Z; }
trait D { type W; }
trait E { type V; }

trait Get { fn ok(&self) -> bool; }

struct W<I>(I);

// `J` is only bound via `K: D<W = J>`, but `I: A<X = <J as B>::Y>` mentions
// `J` inside an alias, which `order_projections` counts as producing `J`.
impl<I, J, K, M> Get for W<I>
where
    K: D<W = J>,
    J: B + E<V = M>,
    I: C<Z = K>,
    I: A<X = <J as B>::Y>,
{
    fn ok(&self) -> bool { true }
}

struct S; struct SK; struct SJ;
impl A for S { type X = u8; }
impl C for S { type Z = SK; }
impl D for SK { type W = SJ; }
impl B for SJ { type Y = u8; }
impl E for SJ { type V = u16; }

fn use_get<G: Get>(g: &G) -> bool { g.ok() }

fn main() { let _ = use_get(&W(S)); }
