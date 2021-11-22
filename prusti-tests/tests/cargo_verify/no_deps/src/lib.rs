use prusti_contracts::*;

#[requires(true)]
#[ensures(true)]
pub fn test() {
    bad_dependency::evil();
}
