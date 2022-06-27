// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

struct S1 {
    x: u32,
}
fn simple_struct_mut() {
    let mut x = S1{ x: 3};
    let mut y = &mut x;
    y.x = 3;
    x.x = 2;
}
fn simple_struct_mut_assert_false() {
    let mut x = S1{ x: 3};
    let mut y = &mut x;
    y.x = 3;
    x.x = 2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn simple_struct_shared() {
    let mut x = S1{ x: 4 };
    let y = &x;
    let z = &x;
}
fn simple_struct_shared_assert_false() {
    let mut x = S1{ x: 4 };
    let y = &x;
    let z = &x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S2<'a> {
    x: &'a mut u32,
}
fn struct_with_mut_reference () {
    let mut n = 4;
    let mut t = S2{ x: &mut n};
}
fn struct_with_mut_reference_assert_false () {
    let mut n = 4;
    let mut t = S2{ x: &mut n};
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S3<'a> {
    x: &'a u32,
}
fn struct_with_shared_reference () {
    let mut n = 4;
    let mut t = S3{ x: &n};
    let mut u = S3{ x: &n};
}
fn struct_with_shared_reference_assert_false () {
    let mut n = 4;
    let mut t = S3{ x: &n};
    let mut u = S3{ x: &n};
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

// FIXME: accessing references of structs panics
// struct S3<'a> {
//     x: &'a mut u32,
// }
// fn struct_with_reference_and_access () {
//     let mut n = 4;
//     let mut t = S2{ x: &mut n};
//     *t.x = 5;
// }
// FIXME: accessing references of structs panics
// fn struct_with_reference_and_access_assert_false () {
//     let mut n = 4;
//     let mut t = S2{ x: &mut n};
//     *t.x = 5;
//     assert!(false);           the asserted expression might not hold
// }
