use prusti_contracts::*;

/// McCarthy’s 91 function
#[ensures(if n <= 101 { result == 91 } else { result == n - 10 })]
fn mc91(n: isize) -> isize {
    if n > 100 {
        n - 10
    } else {
        mc91(mc91(n + 11))
    }
}

fn main() {}
