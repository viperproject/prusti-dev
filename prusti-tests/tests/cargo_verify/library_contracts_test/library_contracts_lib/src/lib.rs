use prusti_contracts::*;

pub enum Opt<T> {
    Some(T),
    None
}

impl<T> Opt<T> {
    #[pure]
    pub fn is_some(&self) -> bool {
        matches!(*self, Opt::Some(..))
    }

    pub fn map<U, F>(self, f: F) -> Opt<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Opt::Some(x) => Opt::Some(f(x)),
            Opt::None => Opt::None,
        }
    }
}

#[trusted]
#[pure]
pub fn demo_fn(_a: u8) -> bool { unimplemented!() }

// Test exporting quantifiers in specs.
// Also test exporting triggers and nested quantifiers.
#[trusted]
#[ensures(forall(|i: u8| i == 0 ==> demo_fn(i)))]
#[ensures(forall(|i: u8| i == 1 ==> forall(|j: u8| j == 1 ==> i == j), triggers=[(demo_fn(i),)]))]
pub fn quantifier_test() {}

// Test exporting quantifiers in predicates.
predicate! {
    pub fn quantifier_predicate(i: u8) -> bool {
        forall(|j: u8| j < i ==> demo_fn(j))
    }
}
