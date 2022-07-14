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
