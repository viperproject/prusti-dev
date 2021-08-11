// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std;

pub trait ToString {
    fn to_string(&self) -> String;
    fn to_sorted_multiline_string(&self) -> String;
}

impl<T, U> ToString for T
where
    T: Clone + Iterator<Item = U>,
    U: std::string::ToString,
{
    fn to_string(&self) -> String {
        self.clone()
            .map(|x| x.to_string())
            .collect::<Vec<String>>()
            .join(", ")
    }
    fn to_sorted_multiline_string(&self) -> String {
        let mut strings = self.clone().map(|x| x.to_string()).collect::<Vec<String>>();
        strings.sort();
        strings.join(",\n")
    }
}
