// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that contains various VIR optimizations.

use crate::{
    config,
    vir::{
        polymorphic_vir::{CfgMethod, Program},
        ToGraphViz,
    },
};
use log::debug;

pub mod bitvectors;
pub mod folding;
pub mod functions;
pub mod methods;
pub mod predicates;
pub mod purification;

fn log_method(
    source_file_name: &str,
    cfg: &CfgMethod,
    optimization_name: &str,
    after_optimization: bool,
) {
    if config::dump_debug_info() {
        let namespace = format!(
            "graphviz_method_optimization_{}_{}",
            optimization_name,
            if after_optimization {
                "after"
            } else {
                "before"
            }
        );
        crate::report::log::report_with_writer(
            &namespace,
            format!("{}.{}.dot", source_file_name, cfg.name()),
            |writer| cfg.to_graphviz(writer),
        );
    }
}

fn log_methods(
    source_file_name: &str,
    cfgs: &[CfgMethod],
    optimization_name: &str,
    after_optimization: bool,
) {
    for cfg in cfgs {
        log_method(source_file_name, cfg, optimization_name, after_optimization);
    }
}

#[tracing::instrument(level = "debug", skip(p))]
pub fn optimize_program(p: Program, source_file_name: &str) -> Program {
    let mut program = p;
    let optimizations = config::optimizations();
    debug!("Enabled optimisations: {:?}", optimizations);

    if config::encode_bitvectors() {
        log_methods(
            source_file_name,
            &program.methods,
            "encode_bitvectors",
            false,
        );
        if bitvectors::uses_bit_operations(&program) {
            bitvectors::replace_all_ints(&mut program);
        }
        log_methods(
            source_file_name,
            &program.methods,
            "encode_bitvectors",
            true,
        );
    }

    // can't borrow self because we need to move fields
    if optimizations.inline_constant_functions {
        log_methods(
            source_file_name,
            &program.methods,
            "inline_constant_functions",
            false,
        );
        let (new_methods, new_functions) =
            functions::inline_constant_functions(program.methods, program.functions);
        program.methods = new_methods;
        program.functions = new_functions;
        log_methods(
            source_file_name,
            &program.methods,
            "inline_constant_functions",
            true,
        );
    }
    if optimizations.optimize_folding {
        log_methods(source_file_name, &program.methods, "folding", false);
        program.methods = program
            .methods
            .into_iter()
            .map(folding::FoldingOptimizer::optimize)
            .collect();
        program.functions = program
            .functions
            .into_iter()
            .map(folding::FoldingOptimizer::optimize)
            .collect();
        log_methods(source_file_name, &program.methods, "folding", true);
    }
    program.methods = program
        .methods
        .into_iter()
        .map(|method| methods::optimize_method_encoding(method, source_file_name, &optimizations))
        .collect();
    if optimizations.delete_unused_predicates {
        program.viper_predicates = predicates::delete_unused_predicates(
            &program.methods,
            &program.functions,
            program.viper_predicates,
        );
    }

    if config::enable_purification_optimization() {
        log_methods(source_file_name, &program.methods, "purify_methods", false);
        program.methods = purification::purify_methods(program.methods, &program.viper_predicates);
        log_methods(source_file_name, &program.methods, "purify_methods", true);
    }

    program
}
