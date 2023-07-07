// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::scala::{self, collection::immutable::Seq};
use duchess::IntoJava;

pub fn new_option<T>(opt: Option<T>) -> scala::Option<T> {
    match opt {
        Some(x) => scala::Some::new(x),
        None => scala::None__::get_module(),
    }
}

impl<T> IntoJava<Seq<T>> for [T] {
    
}
