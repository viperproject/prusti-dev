// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub fn range_extract(mut values: Vec<u128>) -> Vec<(u128, u128)> {
    if values.is_empty() {
        return vec![];
    }
    values.sort();
    let mut ranges = vec![];
    let mut curr_range = (values[0], values[0]);
    for value in values.into_iter().skip(1) {
        if value == curr_range.1 + 1 {
            curr_range.1 += 1;
        } else {
            ranges.push(curr_range);
            curr_range = (value, value);
        }
    }
    ranges.push(curr_range);
    ranges
}