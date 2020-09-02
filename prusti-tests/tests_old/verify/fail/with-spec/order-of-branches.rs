#![allow(dead_code)]
extern crate prusti_contracts;

/// Test that we report errors for the `then` branch before later branches
/// See also issue https://github.com/viperproject/silicon/issues/501

fn test_if_1(b: bool) {
    if b {
        assert!(false); //~ ERROR
    } else {
        assert!(false);
    }
}

#[requires="!b"]
fn test_if_2(b: bool) {
    if b {
        assert!(false);
    } else {
        assert!(false); //~ ERROR
    }
}

fn test_bool_match(b: bool) {
    match b {
        true => assert!(false), //~ ERROR
        false => assert!(false),
    }
}

fn test_repeated_match(v: u32) {
    match v {
        0 => assert!(false), //~ ERROR
        x if x < 5 => assert!(false),
        _ => assert!(false),
    }
}

fn test_match_1(v: u32) {
    match v {
        0 => assert!(false), //~ ERROR
        1 => assert!(false),
        _ => assert!(false),
    }
}

#[requires="v >= 1"]
fn test_match_2(v: u32) {
    match v {
        0 => assert!(false),
        1 => assert!(false), //~ ERROR
        _ => assert!(false),
    }
}

#[requires="v >= 2"]
fn test_match_3(v: u32) {
    match v {
        0 => assert!(false),
        1 => assert!(false),
        _ => assert!(false), //~ ERROR
    }
}

fn test_loop_1(b: bool) {
    while b {
        assert!(false); //~ ERROR
    }
    assert!(false);
}

fn test_loop_2(b: bool) {
    let mut g = true;
    #[invariant="g"] //~ ERROR
    while b {
        g = false;
    }
    assert!(false);
}

#[trusted]
fn main() {}
