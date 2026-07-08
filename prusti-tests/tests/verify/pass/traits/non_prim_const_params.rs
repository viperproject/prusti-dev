#![feature(adt_const_params)]
use std::marker::ConstParamTy;

#[derive(ConstParamTy, PartialEq, Eq)]
struct NotPrim<T> { i: T }

trait Foo<const NONPRIM: NotPrim<i32>> {}
