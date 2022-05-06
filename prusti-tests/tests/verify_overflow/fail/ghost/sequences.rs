// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

type Seq = prusti_contracts::Seq<i32>;
type Map = prusti_contracts::Map<i32, i32>;

#[requires(Map::empty() == Map::empty())]
fn test1() {}

fn main() {}
