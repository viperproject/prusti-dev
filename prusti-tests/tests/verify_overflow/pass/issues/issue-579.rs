use prusti_contracts::*; 

const N: usize = 5;

fn all(a: &[bool; N]) -> bool {
    let mut result = true;
    let mut i = 0;
    while i < N {
        body_invariant!(i < N);
        body_invariant!(result ==> (forall(|j: usize| 0 <= j && j < i ==> a[j])));
        result &= a[i];
        i += 1;
    }
    result
}

#[trusted]
fn main() {}
