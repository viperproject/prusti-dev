
#[requires="n >= 0"]
#[ensures="result == old(n)"]
fn test(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    #[invariant="res == ia"]
    #[invariant="ia <= n"]
    while ia < n {
        res += 1;
        ia += 1;
    }

    res
}

fn main() {

}
