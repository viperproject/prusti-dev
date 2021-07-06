use std::collections::HashMap;

use super::super::polymorphic::*;

pub trait Generic {
    fn substitute(&self, HashMap<TypeVar, Type>) -> &Self;
}