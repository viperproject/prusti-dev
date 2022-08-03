// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;
fn main() {}

enum Enum1 {
    A(i32),
    B(i32),
}

fn test1() {
    let x = Enum1::A(4);
    let y = &x;
}

fn test1_assert_false() {
    let x = Enum1::A(4);
    let y = &x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn test2() {
    let mut x = Enum1::A(4);
    let mut y = &mut x;
    let z = &mut y;
}

fn test2_assert_false() {
    let mut x = Enum1::A(4);
    let mut y = &mut x;
    let z = &mut y;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

enum Enum2<'a> {
    A(&'a mut i32),
    B(&'a i32)
}

fn test3() {
    let mut n = 4;
    let x = Enum2::A(&mut n);
    let y = &x;
}

fn test3_assert_false() {
    let mut n = 4;
    let x = Enum2::A(&mut n);
    let y = &x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn test4() {
    let n = 4;
    let x = Enum2::B(&n);
    let y = &x;
}

fn test4_assert_false() {
    let n = 4;
    let x = Enum2::B(&n);
    let y = &x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn test5() {
    let mut n = 4;
    let mut x = Enum2::A(&mut n);
    let y = &mut x;
}

fn test5_assert_false() {
    let mut n = 4;
    let mut x = Enum2::A(&mut n);
    let y = &mut x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

fn test6() {
    let n = 4;
    let mut x = Enum2::B(&n);
    let y = &mut x;
}

fn test6_assert_false() {
    let n = 4;
    let mut x = Enum2::B(&n);
    let y = &mut x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct A<'a>{
    x: &'a mut i32,
}
struct B<'a>{
    x: &'a mut i32,
}
enum Enum3<'a, 'b> {
    A(&'b mut A<'a>),
    B(&'b mut B<'a>),
}
fn test7(){
    let mut n = 5;
    let mut b = B{ x: &mut n };
    let mut x = Enum3::B(&mut b);
    let y = &mut x;
}
fn test7_assert_false(){
    let mut n = 5;
    let mut b = B{ x: &mut n };
    let mut x = Enum3::B(&mut b);
    let y = &mut x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

struct C<'a>{
    x: &'a mut i32,
}
struct D<'a>{
    x: &'a i32,
}
enum Enum4<'a, 'b> {
    A(&'b mut D<'a>),
    B(&'b C<'a>),
}
fn test8(){
    // Enum with shared reference to struct with mutable reference
    let mut n = 5;
    let mut c = C{ x: &mut n };
    let mut x = Enum4::B(&c);
    let r = &mut x;
}
fn test8_assert_false(){
    let mut n = 5;
    let mut c = C{ x: &mut n };
    let mut x = Enum4::B(&c);
    let r = &mut x;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn test9(){
    // Enum with mutable reference to struct with shared reference
    let n = 5;
    let mut d = D{ x: &n };
    let mut a = Enum4::A(&mut d);
    let r = &mut a;
}
fn test9_assert_false(){
    let n = 5;
    let mut b = D{ x: &n };
    let mut e = Enum4::A(&mut b);
    let r = &mut e;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
fn test10(){
    let n = 5;
    let mut a = D{ x: &n };
    let mut b = &mut a;
    let mut c = &mut b;
    let mut _d = &mut c;
}
fn test10_assert_false(){
    let n = 5;
    let mut a = D{ x: &n };
    let mut b = &mut a;
    let mut c = &mut b;
    let mut _d = &mut c;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

enum Enum5<'a, T> {
    A(&'a mut T),
    B(&'a mut T),
}
fn test11(){
    let mut n = 4;
    let mut c = C{ x: &mut n};
    let mut e = Enum5::A(&mut c);
    let mut f = &mut e;
    let mut g = &mut f;
}
fn test11_assert_false(){
    let mut n = 4;
    let mut c = C{ x: &mut n};
    let mut e = Enum5::A(&mut c);
    let mut f = &mut e;
    let mut g = &mut f;
    assert!(false);      //~ ERROR: the asserted expression might not hold
}
