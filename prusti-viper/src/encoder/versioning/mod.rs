// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir_local;
use vir_crate::polymorphic::{self as vir};

const BUMP_MEM_VERSION_NAME: &str = "builtin$bump_mem_version";

pub fn bump_mem_version_name() -> &'static str {
    BUMP_MEM_VERSION_NAME
}

pub fn bump_mem_version_definition() -> vir::BodylessMethod {
    vir::BodylessMethod {
        name: BUMP_MEM_VERSION_NAME.to_string(),
        formal_args: vec![vir_local! { mem: Ref }],
        formal_returns: vec![],
        pres: vec![],
        posts: vec![],
    }
}
