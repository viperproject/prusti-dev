extern crate prusti_contracts;

#[requires="n >= 0"]
#[ensures="result == old(n) * (1 + old(n) * (1 + old(n)))"]
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="n == old(n)"]
    #[invariant="res == ia * (1 + n * (1 + n))"]
    #[invariant="ia <= n"]
    while ia < n {
        res += 1;
        let mut ib = 0;

        #[invariant="n == old(n)"]
        #[invariant="res == ia * (1 + n * (1 + n)) + 1 + ib * (1 + n)"]
        #[invariant="ib <= n"]
        while ib < n {
            res += 1;
            let mut ic = 0;

            #[invariant="n == old(n)"]
            #[invariant="ic <= n && res == ia * (1 + n * (1 + n)) + 1 + ib * (1 + n) + 1 + ib"]
            while ic < n {
                res += 1;
                ic += 1;
            }

            ib += 1;
        }

        ia += 1;
    }

    res
}

fn main() {

}
