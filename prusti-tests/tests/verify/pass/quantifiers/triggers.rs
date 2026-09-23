use prusti_contracts::*;

#[pure]
#[trusted]
fn len(a: u32) -> usize { 0 }

#[pure]
#[trusted]
#[requires(i < len(a))]
fn lookup(a: u32, i: usize) -> i32 { 0 }

/// A trigger mentioning a captured variable and the bound variable resolves to
/// the same term as the one the caller has, so the quantifier is instantiated.
#[requires(forall(|i: usize| i < len(a) ==> lookup(a, i) > 0, triggers = [(lookup(a, i),)]))]
#[requires(len(a) > 3)]
fn instantiated(a: u32) {
    prusti_assert!(lookup(a, 2) > 0);
}

/// A multi-trigger over two bound variables, chained through a framing
/// quantifier: proving `b` sorted needs `lookup(b, _)` to bring `lookup(a, _)`
/// into scope, which in turn fires the sortedness of `a`.
#[requires(len(a) == len(b))]
#[requires(forall(|i: usize, j: usize| (i < j && j < len(a)) ==> lookup(a, i) <= lookup(a, j),
                  triggers = [(lookup(a, i), lookup(a, j))]))]
#[requires(forall(|i: usize| i < len(a) ==> lookup(b, i) == lookup(a, i),
                  triggers = [(lookup(b, i),)]))]
fn framed(a: u32, b: u32) {
    prusti_assert!(forall(|i: usize, j: usize| (i < j && j < len(b)) ==> lookup(b, i) <= lookup(b, j),
                          triggers = [(lookup(b, i), lookup(b, j))]));
}

/// Triggers are also forwarded for `exists`.
#[requires(exists(|i: usize| lookup(a, i) == 42, triggers = [(lookup(a, i),)]))]
fn existential(a: u32) {}
