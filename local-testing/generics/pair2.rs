use prusti_contracts::*;

struct Pair<T, U> {
    first: T,
    second: U,
}

#[requires(pair.second == true)]
#[ensures(result.second == true)]
fn copy_pair<T>(pair: Pair<T, bool>) -> Pair<T, bool> {
    Pair {
        first: pair.first,
        second: pair.second
    }
}

fn fst<T, U>(pair: Pair<T, U>) -> T {
  let unused = pair.second;
  pair.first
}

#[ensures(result == true)]
fn client() -> bool {
    let initial_pair = Pair {
        first: 42u32,
        second: true
    };
    let copied_pair = copy_pair(initial_pair);
    copied_pair.second
}

fn main() {
    let pair = Pair { first: 1, second: 2 };
    fst(pair);
}
