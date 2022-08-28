// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

enum Something {
    First,
    Second,
    Third,
}

#[ensures(result)]
fn test1(x: Something) -> bool {
    !matches!(x, Something::Third)
}

/*
FIXME: unhandled verification error: Exhale might fail. There might be insufficient 
permission to access MemoryBlock(_5$address, Size$Bool$(constructor$Snap$Usize$(1)))

#[ensures(result)]
fn test2(x: Something, y: Something) -> bool {
    matches!(x, Something::First) || !matches!(y, Something::First)
}
*/

fn main() {}
