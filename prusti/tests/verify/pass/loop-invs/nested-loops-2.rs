extern crate prusti_contracts;

#[requires="n >= 0"]
#[ensures="k >= 0 ==> result >= 0"]
fn test(n: i32, k: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="n == old(n)"] // TODO: remove this
    #[invariant="k == old(k)"] // TODO: remove this
    #[invariant="ia <= n"]
    #[invariant="k >= 0 ==> res >= 0"]
    while ia < n {
        res += 1;
        let mut ib = 0;

        #[invariant="n == old(n)"] // TODO: remove this
        #[invariant="k == old(k)"] // TODO: remove this
        #[invariant="ib <= n"]
        #[invariant="k >= 0 ==> res >= 0"]
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
