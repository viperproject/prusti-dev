use prusti_contracts::*;

struct IterRange {
    from: usize,
    to: usize,
}

#[requires(iter.from < iter.to)] // WRONG, should be `<=`
#[ensures(iter.to == old(iter.to))]
#[ensures(old(iter.from < iter.to) ==> iter.from == old(iter.from) + 1)]
#[ensures(old(iter.from < iter.to) == matches!(result, Some(_)))]
#[ensures(old(iter.from == iter.to) == matches!(result, None))]
fn next(iter: &mut IterRange) -> Option<usize> {
    if iter.from < iter.to {
        let v = iter.from;
        iter.from = v + 1;
        Some(v)
    } else {
        None
    }
}

fn main() {
    let mut iter = IterRange { from: 0, to: 10 };
    let mut i = 0;
    loop {
        body_invariant!(i == iter.from && iter.from <= iter.to && iter.to == 10);
        match next(&mut iter) { //~ ERROR: precondition might not hold
            Some(_) => {}
            None => break,
        }
        i += 1;
    }
    assert!(i == 10);
}
