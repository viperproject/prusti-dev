// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic as vir;

pub const BUMP_MEM_VERSION_METHOD_NAME: &str = "builtin$bump_mem_version";
const MEM_VERSION_FIELD_NAME: &str = "version";
pub const MEM_VERSION_VAR_NAME: &str = "mem";
pub const MEM_VERSION_VAR_TYPE: vir::Type = vir::Type::Ref;

/// Returns the local variable that holds the memory version in impure methods
pub fn encode_mem_version_var() -> vir::LocalVar {
    vir::LocalVar::new(
        MEM_VERSION_VAR_NAME.to_string(),
        MEM_VERSION_VAR_TYPE,
    )
}

/// Returns the field that encodes the memory version in impure methods
fn encode_mem_version_field() -> vir::Field {
    vir::Field {
        name: MEM_VERSION_FIELD_NAME.to_string(),
        typ: vir::Type::Int,
    }
}

/// Returns the expression that encodes the memory version in impure methods
pub fn encode_mem_version_expr() -> vir::Expr {
    vir::Expr::from(encode_mem_version_var())
        .field(encode_mem_version_field())
}

fn encode_mem_version_expr_permissions() -> vir::Expr {
    vir::Expr::acc_permission(
        encode_mem_version_expr(),
        vir::PermAmount::Write
    )
}

/// Statements that encode the memory version at the beginning of a method
pub fn encode_mem_version_init() -> Vec<vir::Stmt> {
    vec![vir::Stmt::inhale(encode_mem_version_expr_permissions())]
}

/// Returns definition of the method that updates the memory version
pub fn encode_bump_mem_version_method_def() -> vir::BodylessMethod {
    vir::BodylessMethod {
        name: BUMP_MEM_VERSION_METHOD_NAME.to_string(),
        formal_args: vec![encode_mem_version_var()],
        formal_returns: vec![],
        pres: vec![encode_mem_version_expr_permissions()],
        posts: vec![encode_mem_version_expr_permissions()],
    }
}
