// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub(super) mod interface;

use prusti_common::vir_local;
use vir_crate::polymorphic::{self as vir};

const TICK_NAME: &str = "builtin$tick";

pub fn tick_name() -> &'static str {
    TICK_NAME
}

pub fn tick_definition() -> vir::BodylessMethod {
    let n = vir_local! { n: {vir::Type::Int} };
    vir::BodylessMethod {
        name: TICK_NAME.to_string(),
        formal_args: vec![n.clone()],
        formal_returns: vec![],
        pres: vec![
            vir::Expr::ge_cmp(n.clone().into(), 0.into()),
            vir::Expr::resource_access_predicate(
                vir::common::ResourceType::TimeCredits,
                n.clone().into(),
            ),
        ],
        posts: vec![vir::Expr::resource_access_predicate(
            vir::common::ResourceType::TimeReceipts,
            n.clone().into(),
        )],
    }
}
