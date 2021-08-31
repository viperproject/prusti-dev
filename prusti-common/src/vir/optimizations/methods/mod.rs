// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that contains optimizations for methods.

mod cfg_cleaner;
mod empty_if_remover;
mod assert_remover;
mod var_remover;
mod purifier;
mod quantifier_fixer;

use crate::config::Optimizations;
use crate::vir::polymorphic_vir::cfg::CfgMethod;
use super::log_method;

use self::cfg_cleaner::clean_cfg;
use self::empty_if_remover::remove_empty_if;
use self::assert_remover::remove_trivial_assertions;
use self::var_remover::remove_unused_vars;
use self::purifier::purify_vars;
use self::quantifier_fixer::fix_quantifiers;

#[allow(clippy::let_and_return)]
pub fn optimize_method_encoding(cfg: CfgMethod, source_file_name: &str, optimizations: &Optimizations) -> CfgMethod {
    macro_rules! apply {
        ($optimization: ident, $cfg: ident) => {
            if optimizations.$optimization {
                log_method(source_file_name, &$cfg, stringify!($optimization), false);
                let optimized_cfg = $optimization($cfg);
                log_method(source_file_name, &optimized_cfg, stringify!($optimization), true);
                optimized_cfg
            } else {
                $cfg
            }
        };
    }
    let cfg = apply!(purify_vars, cfg);
    let cfg = apply!(fix_quantifiers, cfg);
    let cfg = apply!(remove_empty_if, cfg);
    let cfg = apply!(remove_unused_vars, cfg);
    let cfg = apply!(remove_trivial_assertions, cfg);
    let cfg = apply!(clean_cfg, cfg);

    cfg
}
