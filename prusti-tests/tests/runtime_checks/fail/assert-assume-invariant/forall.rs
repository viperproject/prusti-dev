//@run: 101
use prusti_contracts::*;
#[trusted]
fn main() {
    let v = vec![1,2,3,4,5,6];
    prusti_assume!(#[insert_runtime_check]forall(|x: usize| x < 6 ==> v[x] < 6));
}
