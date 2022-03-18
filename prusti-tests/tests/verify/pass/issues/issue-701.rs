use prusti_contracts::*;

struct Wrapper {
    inner: Inner
}

enum Inner {
    SomeThing(Thing), Default
}

struct Thing {}

#[pure]
#[requires(matches!(&m.inner, Inner::SomeThing(_)))]
fn misbehavior_invariant(m: &Wrapper) -> bool {
    match &m.inner {
        Inner::SomeThing(t) => 1,
        _ => unreachable!()
    };
    true
}

fn main(){}
