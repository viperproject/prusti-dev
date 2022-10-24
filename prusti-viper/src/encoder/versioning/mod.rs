// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir_local;
use vir_crate::polymorphic::{self as vir};

pub fn define_bump_version_method() -> vir::BodylessMethod {
    vir::BodylessMethod {
        name: "builtin$bump_version".to_string(),
        formal_args: vec![],
        formal_returns: vec![vir_local!{ ret: {return_type} }],
    }
}
