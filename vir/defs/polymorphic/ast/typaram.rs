// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use regex::Regex;
use std::collections::HashMap;

pub struct Substs {
    regex: Regex,
    repls: HashMap<String, String>,
}
