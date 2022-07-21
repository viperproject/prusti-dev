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
    assert!(z.x == 4);
}
fn simple_struct_shared_assert_false() {
    let mut x = S1{ x: 4 };
    let y = &x;
    let z = &x;
    assert!(z.x == 5);      //~ ERROR: the asserted expression might not hold
}

struct S2<'a> {
    x: &'a mut u32,
}
fn struct_with_mut_reference () {
    let mut n = 4;
    let t = S2{ x: &mut n};
    let u = &t;
}
fn struct_with_mut_reference_assert_false () {
    let mut n = 4;
    let mut t = S2{ x: &mut n};
    let u = &t;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn struct_shared_references(){
    let mut n = 4;
    let s1 = S2{ x: &mut n};
    let s2 = &s1;
    let s3 = &s2;
    let _s4 = &s3;
}
fn struct_shared_references_assert_false(){
    let mut n = 4;
    let s1 = S2{ x: &mut n};
    let s2 = &s1;
    let s3 = &s2;
    let _s4 = &s3;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S3<'a> {
    x: &'a u32,
}
fn struct_with_shared_reference () {
    let n = 4;
    let mut t1 = S3{ x: &n};
    let mut t2 = S3{ x: &n};
    let u = &mut t2;
}
fn struct_with_shared_reference_assert_false () {
    let n = 4;
    let mut t1 = S3{ x: &n};
    let mut t2 = S3{ x: &n};
    let u = &mut t2;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn struct_mut_references(){
    let n = 4;
    let mut s1 = S3{ x: &n};
    let mut s2 = &mut s1;
    let mut s3 = &mut s2;
    let mut s4 = &mut s3;
}
fn struct_mut_references_assert_false(){
    let n = 4;
    let mut s1 = S3{ x: &n};
    let mut s2 = &mut s1;
    let mut s3 = &mut s2;
    let mut _s4 = &mut s3;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S4I<'a> {
    x: &'a mut u32,
}
struct S4O<'a, 'b> {
    x: &'b mut S4I<'a>,
}
fn nested_struct_with_mutable_reference () {
    let mut n = 4;
    let mut i = S4I { x: &mut n };
    let mut o = S4O { x: &mut i };
}
fn nested_struct_with_mutable_reference_assert_false () {
    let mut n = 4;
    let mut i = S4I { x: &mut n };
    let mut o = S4O { x: &mut i };
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S5I<'a> {
    x: &'a u32,
}
struct S5O<'a, 'b> {
    x: &'b S5I<'a>,
}
fn nested_struct_with_shared_reference () {
    let n = 4;
    let i = S5I { x: &n };
    let o = S5O { x: &i };
}
fn nested_struct_with_shared_reference_assert_false () {
    let n = 4;
    let i = S5I { x: &n };
    let o = S5O { x: &i };
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S6<'a, 'b: 'a, 'c: 'b> {
    x: &'a i32,
    y: &'b i32,
    z: &'c i32,
}
fn struct_with_subset_lifetime() {
    let x = 5;
    let y = 6;
    let z = 7;
    let s = S6 {
        x: &x,
        y: &y,
        z: &z,
    };
}
fn struct_with_subset_lifetime_assert_false() {
    let x = 5;
    let y = 6;
    let z = 7;
    let s = S6 {
        x: &x,
        y: &y,
        z: &z,
    };
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S7_1<'a> {
    x: &'a mut u32,
}
struct S7_2<'a, 'b> {
    x: &'b mut S7_1<'a>,
}
struct S7_3<'a, 'b, 'c> {
    x: &'c mut S7_2<'a, 'b>,
}
fn test_deeply_nested(){
    let mut n = 4;
    let mut s1 = S7_1{ x: &mut n };
    let mut s2 = S7_2{ x: &mut s1 };
    let mut s3 = S7_3{ x: &mut s2 };
}
fn test_deeply_nested_assert_false(){
    let mut n = 4;
    let mut s1 = S7_1{ x: &mut n };
    let mut s2 = S7_2{ x: &mut s1 };
    let mut s3 = S7_3{ x: &mut s2 };
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct S8<'a, T> {
    x: &'a mut T,
}
struct X8<'a> {
    x: &'a mut i32,
}
fn test_generic_struct_assert_false(){
    let mut n = 4;
    let mut x = X8{ x: &mut n };
    let mut s1 = S8{ x: &mut x };
    let mut s2 = &mut s1;
}
fn test_generic_struct(){
    let mut n = 4;
    let mut x = X8{ x: &mut n };
    let mut s1 = S8{ x: &mut x };
    let mut s2 = &mut s1;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

// FIXME: Nested structs with "shared" lifetimes don't work due to "lifetime extension"
// struct S6I<'a> {
//     x: &'a u32,
// }
// struct S6O<'a> {
//     x: &'a S6I<'a>,
// }
// fn nested_struct_same_lifetime_with_shared_reference () {
//     let n = 4;
//     let i = S6I { x: &n };
//     let o = S6O { x: &i };
// }
// fn nested_struct_same_lifetime_with_shared_reference_assert_false () {
//     let n = 4;
//     let i = S6I { x: &n };
//     let o = S6O { x: &i };
//     assert!(false);            the asserted expression might not hold
// }

// FIXME: accessing references of structs panics
// struct S7<'a> {
//     x: &'a mut u32,
// }
// fn struct_with_reference_and_access () {
//     let mut n = 4;
//     let mut t = S7{ x: &mut n};
//     *t.x = 5;
// }
// FIXME: accessing references of structs panics
// fn struct_with_reference_and_access_assert_false () {
//     let mut n = 4;
//     let mut t = S7{ x: &mut n};
//     *t.x = 5;
//     assert!(false);           the asserted expression might not hold
// }
