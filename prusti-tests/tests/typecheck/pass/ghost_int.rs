use prusti_contracts::GhostInt;
use prusti_contracts::*;

fn test_1() -> GhostInt{
    let x = GhostInt::new(10);
    let y = GhostInt::new(20);
    x + y
}

#[ensures(result == gh1 + gh2)]
fn test_2(gh1: GhostInt, gh2: GhostInt) -> GhostInt{
   gh1 + gh2
}

fn main() {}
