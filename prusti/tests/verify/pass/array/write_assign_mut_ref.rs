extern crate prusti_contracts;

// Same as write_assign, but using assigning through &mut where it is possible

fn assigned_fixed_lit_mut_ref(arr: &mut [isize; 64]) {
    let a = &mut arr[42];
    *a = 1234;
}
// TODO: These three tests do not verify due to a fold that is done before exhaling the permissions. 
// The same error seems to happen if we using something else than an array
/*
fn assign_fixed_mut_ref(arr: &mut [isize; 64], value: isize) {
    let a = &mut arr[42];
    *a = value;
}

// We need i >= 0 because unsigned integers bounds are not encoded by default
#[requires="0 <= i && i < 64"]
fn assign_nth(arr: &mut [isize; 64], i: usize, value: isize) {
    let a = &mut arr[i];
    *a = value;
}

// TODO: this one generate wrong encoding:
// _11.val_ref := _1.val_ref.val_array[_12].val_ref
// _11.val_ref := _15
// Doesn't affect the underlying array
// Last line should be _11.val_ref.val_int := _15.val_int
#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn assign_many(arr: &mut [isize; 64], i: usize, j: usize, k: usize, value: isize) {
    let a = &mut arr[i];
    *a = value;
    let b = &mut arr[j];
    *b = value;
    let c = &mut arr[k];
    *c = value;
}
*/
// TODO: this one should be verified
/*
#[requires="0 <= i && i < 64"]
#[requires="0 <= j && j < 64"]
#[requires="0 <= k && k < 64"]
fn assign_many_lit(arr: &mut [isize; 64], i: usize, j: usize, k: usize) {
    let a = &mut arr[i];
    *a = 123;
    let b = &mut arr[j];
    *b = 456;
    let c = &mut arr[k];
    *c = 789;
}
*/
fn main() {}