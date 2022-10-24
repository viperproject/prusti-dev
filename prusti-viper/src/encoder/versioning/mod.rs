// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir_local;
use vir_crate::polymorphic as vir;

const BUMP_MEM_VERSION_NAME: &str = "builtin$bump_mem_version";
const MEM_VERSION_FIELD_NAME: &str = "version";

pub fn get_bump_mem_version_method_name() -> String {
    BUMP_MEM_VERSION_NAME.to_string()
}

pub fn get_mem_version_field_name() -> String {
    MEM_VERSION_FIELD_NAME.to_string()
}

pub fn get_mem_version_field_def() -> vir::Field {
    vir::Field {
        name: get_mem_version_field_name(),
        typ: vir::Type::Int,
    }
}

pub fn get_bump_mem_version_method_def() -> vir::BodylessMethod {
    let name = get_bump_mem_version_method_name();
    let mem_arg = vir_local!{ mem: Ref };
    let mem_version_field = get_mem_version_field_def();
    let mem_version_place = vir::Expr::from(mem_arg.clone()).field(mem_version_field);
    vir::BodylessMethod {
        name,
        formal_args: vec![mem_arg],
        formal_returns: vec![],
        pres: vec![vir::Expr::acc_permission(
            mem_version_place.clone(),
            vir::PermAmount::Write
        )],
        posts: vec![vir::Expr::acc_permission(
            mem_version_place,
            vir::PermAmount::Write
        )],
    }
}
