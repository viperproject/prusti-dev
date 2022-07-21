// ignore-test https://rust-lang.zulipchat.com/#narrow/stream/182449-t-compiler.2Fhelp/topic/Resolving.20a.20.60clone.60.20call.20to.20a.20.60DefId.60/near/290366147

#![feature(allocator_api)]

use prusti_contracts::*;

use std::vec::Vec;

#[extern_spec]
impl<T: Clone, A: std::alloc::Allocator + Clone> Clone for Vec<T, A> {
    #[ensures(true)]
    fn clone<'a>(&'a self) -> Self;
}

#[extern_spec]
impl<T> Clone for Option<T> {
    #[ensures(true)]
    fn clone(&self) -> Option::<T>
        where T: std::clone::Clone;
}

fn main() {}
