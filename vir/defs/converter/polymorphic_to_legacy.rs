use std::collections::HashMap;

use super::super::polymorphic::*;
use super::super::polymorphic;
use super::super::legacy;

pub trait Generic {
    fn substitute(&self, HashMap<TypeVar, Type>) -> &Self;
}