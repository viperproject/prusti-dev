use prusti_contracts::*;

#[requires(n >= 0)]
#[ensures(result == old(n))]
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        body_invariant!(res == ia);
        body_invariant!(ia < n);
        res += 1;

        while false {
            body_invariant!(true);
        }

        ia += 1;
    }

    res
}

fn main() {

}
