// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty;
use rustc::middle::const_val::ConstInt;


pub fn const_int_is_zero(const_int: &ConstInt) -> bool {
    match const_int {
        &ConstInt::I32(val) => val == (0 as i32),
        &ConstInt::U8(val) => val == (0 as u8),
        &ConstInt::Isize(val) => val.as_i64() == (0 as i64),
        x => unimplemented!("{:?}", x),
    }
}
