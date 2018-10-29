extern crate prusti_contracts;

#[requires="n >= 0"]
#[ensures="result == old(n) * (1 + old(n) * old(k))"]
fn test(n: i32, k: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="n == old(n)"] // TODO: remove this
    #[invariant="k == old(k)"] // TODO: remove this
    #[invariant="res == ia * (1 + n * k)"]
    #[invariant="ia <= n"]
    while ia < n {
        res += 1;
        let mut ib = 0;

        #[invariant="n == old(n)"] // TODO: remove this
        #[invariant="k == old(k)"] // TODO: remove this
        #[invariant="res == ia * (1 + n * k) + 1 + ib * k"]
        #[invariant="ib <= n"]
        while ib < n {
            res += k;
            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {

}
