use prusti_contracts::*;

#[requires(n >= 0)]
#[ensures(k >= 0 ==> result >= 0)]
fn test(n: i32, k: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        body_invariant!(n == old(n)); // TODO: remove this once encoding of
                                      // loops without back-edges is stable.
        body_invariant!(k == old(k)); // TODO: remove this
        body_invariant!(ia <= n);
        body_invariant!(k >= 0 ==> res >= 0);
        res += 1;
        let mut ib = 0;

        while ib < n {
            body_invariant!(n == old(n)); // TODO: remove this
            body_invariant!(k == old(k)); // TODO: remove this
            body_invariant!(ib <= n);
            body_invariant!(k >= 0 ==> res >= 0);
            res += k;
            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {

}
