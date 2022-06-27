// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn main() {}

#[derive(Clone)]
struct I32Container<i32>(i32);

#[derive(Clone)]
struct Container<T>(T);
fn container_client(){
    let x: i32 = 4;
    let c: Container<i32> = Container(x);
    let d = c.clone();
}
fn container_client_assert_false(){
    let x: i32 = 4;
    let c: Container<i32> = Container(x);
    let d = c.clone();
    assert!(false);      //~ ERROR: the asserted expression might not hold
}

#[derive(Clone)]
struct Container2<T,U>{
    t: T,
    u: U,
}

// NOTE: The following implementation was generated with "cargo-expand" and has been
//   slightly modified to include the assert!(false)
struct Container3<T>(T);
impl<T: ::core::clone::Clone> ::core::clone::Clone for Container3<T> {
    #[inline]
    fn clone(&self) -> Container3<T> {
        let x = match *self {
            Self(ref __self_0_0) => Container3(::core::clone::Clone::clone(&(*__self_0_0))),
        };
        assert!(false);      //~ ERROR: the asserted expression might not hold
        x
    }
}


