#![feature(unboxed_closures)]
#![feature(fn_traits)]

use prusti_contracts::*;

fn main() {}

// split into many functions to avoid exponential branching complexity

fn test_1() {
    let some = Some(42);
    let none = Option::<i32>::None;

    assert!(some.is_some());
    assert!(!some.is_none());
    assert!(!none.is_some());
    assert!(none.is_none());

    assert!(some.as_ref().is_some());
    //let x = some.as_ref().unwrap();
    //assert!(*x == 42);
    //assert!(*some.as_ref().unwrap() == 42);
    assert!(none.as_ref().is_none());

    assert!(some.unwrap() == 42);
    assert!(some.expect("test") == 42);
    assert!(some.unwrap_or(69) == 42);
    assert!(none.unwrap_or(69) == 69);
    assert!(some.unwrap_or_else(|| 69) == 42);
    let _ = none.unwrap_or_else(|| 69);
    assert!(some.unwrap_or_default() == 42);
    assert!(none.unwrap_or_default() == 0);
    unsafe {
        assert!(some.unwrap_unchecked() == 42);
    }
}

fn test_2() {
    let some = Some(42);
    let none = Option::<i32>::None;

    assert!(some.map(|x| x + 1).is_some());
    let _ = some.map_or(69, |x| x + 1);
    assert!(none.map_or(69, |x| x + 1) == 69);
    let _ = some.map_or_else(|| 42, |x| x + 1);

    let ok: Result<i32, bool> = Ok(42);
    let err: Result<i32, bool> = Err(false);
    assert!(some.ok_or(false) == ok);
    assert!(none.ok_or(false) == err);
    assert!(some.ok_or_else(|| true) == ok);
    assert!(none.ok_or_else(|| true).is_err());
}

fn test_3() {
    let some = Some(42);
    let none = Option::<i32>::None;

    assert!(some.and(some).unwrap() == 42);
    assert!(some.and(none).is_none());
    assert!(none.and(some).is_none());
    assert!(none.and(none).is_none());

    let _ = some.and_then(|v| Some(v));
    let _ = some.and_then(|_| Option::<i32>::None);
    assert!(none.and_then(|v| Some(v)).is_none());
    assert!(none.and_then(|_| Option::<i32>::None).is_none());
}

fn test_4() {
    let some = Some(42);
    let none = Option::<i32>::None;

    // manual predicate

    struct Equals42;

    impl FnOnce<(&i32,)> for Equals42 {
        type Output = bool;
        #[trusted]
        extern "rust-call" fn call_once(self, arg: (&i32,)) -> bool {
            *arg.0 == 42
        }
    }

    let filtered = some.filter(Equals42);
    assert!(match filtered {
        Some(v) => v == 42,
        None => true, // can't yet prove that Equals42 succeeds
    });
    assert!(none.filter(Equals42) == none);
}

fn test_5() {
    let some = Some(42);
    let some_2 = Some(2);
    let none = Option::<i32>::None;

    assert!(some.or(some_2) == some);
    assert!(none.or(some_2) == some_2);
    assert!(some.or(none) == some);
    assert!(none.or(none) == none);

    assert!(some.xor(some) == none);
    assert!(none.xor(some) == some);
    assert!(some.xor(none) == some);
    assert!(none.xor(none) == none);
}

fn test_6() {
    let some = Some(42);
    let none = Option::<i32>::None;

    let mut opt = none;
    let val = opt.insert(1);
    assert!(*val == 1);
    *val = 42;
    assert!(opt == some);

    let mut opt = some;
    assert!(*opt.get_or_insert(0) == 42);
    assert!(opt == some);
    let mut opt = none;
    let val = opt.get_or_insert(0);
    assert!(*val == 0);
    *val += 1;
    assert!(opt.unwrap() == 1);

    let mut opt = some;
    assert!(*opt.get_or_insert_with(|| 0) == 42);
    assert!(opt == some);

    let mut opt = none;
    *opt.get_or_insert_with(|| 0) = 42;
    assert!(opt == some);

    let mut opt = some;
    assert!(opt.take() == some);
    assert!(opt == none);
    assert!(opt.take() == none);
    assert!(opt == none);

    let mut opt = none;
    assert!(opt.replace(42) == none);
    assert!(opt == some);
    assert!(opt.replace(1) == some);
    assert!(opt.unwrap() == 1);

    let pair = (42, 42);
    assert!(some.zip(some).unwrap() == pair);
    assert!(some.zip(none).is_none());
    assert!(none.zip(some).is_none());
    assert!(none.zip(none).is_none());
}

fn test_flatten() {
    let x: Option<Option<u32>> = Some(Some(6));
    assert!(x.flatten().unwrap() == 6);

    let x: Option<Option<u32>> = Some(None);
    assert!(x.flatten().is_none());

    let x: Option<Option<u32>> = None;
    assert!(x.flatten().is_none());

    let x: Option<Option<Option<u32>>> = Some(Some(Some(6)));
    assert!(x.flatten().unwrap().unwrap() == 6);
    assert!(x.flatten().flatten().unwrap() == 6);
}

fn test_transpose() {
    #[derive(Debug, Eq, PartialEq)]
    struct SomeErr;

    let x: Result<Option<i32>, SomeErr> = Ok(Some(5));
    let y: Option<Result<i32, SomeErr>> = Some(Ok(5));
    let y = y.transpose();
    prusti_assert!(x === y);
}
