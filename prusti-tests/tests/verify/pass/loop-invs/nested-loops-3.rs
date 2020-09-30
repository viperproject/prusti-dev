use prusti_contracts::*;

#[requires(n >= 0)]
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        body_invariant!(n == old(n));
        res += 1;
        let mut ib = 0;

        while ib < n {
            body_invariant!(n == old(n));
            res += 1;
            let mut ic = 0;

            while ic < n {
                body_invariant!(n == old(n));
                res += 1;
                ic += 1;
            }

            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {}
