use prusti_contracts::*;

fn main() {
    let a: i32 = i32::from(true);
    assert!(a == 1);
    let b: i32 = i32::from(false);
    assert!(b == 0);
    let c: i32 = i32::from(7u8);
    assert!(c == 7);
    let d: i32 = i32::from(9u16);
    assert!(d == 9);
}

// `extern_spec` for the impls of a *foreign* generic trait (`core`'s
// `From<T>`), covering several distinct type arguments.
#[extern_spec]
impl From<bool> for i32 {
    #[trusted]
    #[ensures(result == if source { 1 } else { 0 })]
    fn from(source: bool) -> i32;
}

#[extern_spec]
impl From<u8> for i32 {
    #[trusted]
    #[ensures(result == source as i32)]
    fn from(source: u8) -> i32;
}

#[extern_spec]
impl From<u16> for i32 {
    #[trusted]
    #[ensures(result == source as i32)]
    fn from(source: u16) -> i32;
}
