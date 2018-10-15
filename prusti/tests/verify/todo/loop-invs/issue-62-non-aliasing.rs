//! Issue #62: "Non-aliasing info are needed"

extern crate prusti_contracts;

#[requires="n >= 0"]
#[ensures="result == old(n) * (1 + old(n) * old(k))"]
fn test(n: i32, k: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="res == ia * (1 + n * k)"]
    #[invariant="ia <= n"]
    while ia < n {
        res += 1;
        let mut ib = 0;

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

/*
    An extract:

    ```viper
    // Initially we have no predicate permissions
    assert perm(int(_1)) == 0/1
    assert perm(int(_2)) == 0/1

    // Here we would like to say that _1 != _2
    inhale acc(int(_1), 1 / 1) && acc(int(_2), 1 / 1)

    // ...but any the following fails
    assert _1 != _2
    assert perm(int(_1)) == 1/1
    ```
*/
