//ignore-test "unique borrows" no longer exist in MIR, detecting this is more difficult

// Copyright 2016 lazy-static.rs Developers
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::sync::Once;
use std::sync::ONCE_INIT;
use std::hint::unreachable_unchecked;

pub struct Lazy<T: Sync>(Option<T>, Once);

impl Lazy<u32> {
    pub const INIT: Self = Lazy(None, ONCE_INIT);

    #[inline(always)]
    pub fn get(&'static mut self)
    {
        {
            let r = &mut self.0;
            self.1.call_once(|| { //~ ERROR unsuported creation of unique borrows (implicitly created in closure bindings)
                *r = None; //~ ERROR determining the region of a dereferentiation is not supported
            });
        }
    }
}

fn main() {}
