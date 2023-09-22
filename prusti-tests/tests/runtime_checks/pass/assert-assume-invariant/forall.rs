//@run
use prusti_contracts::*;
#[trusted]
fn main() {
    let v = vec![1,2,3,4,5,6];
    // success, all elements of v are smaller-eq than 6
    prusti_assume!(forall(|x: usize| x < 6 ==> v[x] <= 6));
}
