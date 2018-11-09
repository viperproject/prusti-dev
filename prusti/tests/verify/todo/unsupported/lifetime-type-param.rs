/// Source: https://github.com/tokio-rs/tokio/blob/f929576f0ea0debedd31cccd9b5a336ea1687568/tokio-io/src/lib.rs#L64
extern crate prusti_contracts;
use std::io;

pub trait AsyncRead: std::io::Read {}

pub trait AsyncWrite: std::io::Write {}

#[trusted]
fn _assert<T>() {}

fn _assert_objects() {
    _assert::<Box<AsyncRead>>();
    _assert::<Box<AsyncWrite>>();
}

fn main() {}
