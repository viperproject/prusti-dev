use prusti_contracts::*;

resource! {
    fn rsrc(amount: usize);
}

obligation! {
    fn obl(amount: usize, place: usize);
}

fn main() {
    before_expiry(33); //~ ERROR using the built-in `before_expiry` in non-specification code is not allowed

    old(34); //~ ERROR using the built-in `old` in non-specification code is not allowed

    forall(0, 0); //~ ERROR using the built-in `forall` in non-specification code is not allowed

    exists("the", "end"); //~ ERROR using the built-in `exists` in non-specification code is not allowed

    snap(&(1 + 1)); //~ ERROR using the built-in `snap` in non-specification code is not allowed

    snapshot_equality(1 + 1, 3); //~ ERROR using the built-in `snapshot_equality` in non-specification code is not allowed

    rsrc(12); //~ ERROR using a resource in non-specification code is not allowed

    obl(42, 33); //~ ERROR using an obligation in non-specification code is not allowed

    time_credits(5); //~ ERROR using a resource in non-specification code is not allowed
}
