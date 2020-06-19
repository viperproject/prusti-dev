// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Make sure that all local variables assigned inside the loops are havocked.

use std::collections::{HashMap, HashSet};
use super::super::{ast, cfg};
use log::trace;

/// Once we cut the back-edges, Viper does not havoc the local variables assigned inside loops
/// anymore and we need to do that manually.
///
/// Algorithm:
///
/// 1.  Create a map that gives predecessors of a specific block.
/// 2.  For each back-edge, iterate from the back edge backward until
///     the loop head. All visited blocks belong to the loop.
/// 3.  While traversing the blocks, collect all assigned pure variables.
/// 4.  Havoc the collected variables in the loop head.
pub fn havoc_assigned_locals(
    method: &mut cfg::CfgMethod,
    havoc_methods: &HashMap<ast::TypeId, String>,
) {
    trace!("[enter] havoc_assigned_locals({})", method.name());
    let _predecessors = method.predecessors();
    let loop_vars = Vec::new();
    for (_index, _block) in method.basic_blocks.iter().enumerate() {
        /*
        if let cfg::Successor::BackEdge(target) = block.successor {
            let vars = collect_assigned_vars(method, index, target.block_index, &predecessors);
            loop_vars.push((target.block_index, vars));
        }
        */
    }
    for (loop_head, vars) in loop_vars {
        add_havoc_stmts(method, loop_head, vars, havoc_methods);
    }
    trace!("[exit] havoc_assigned_locals({})", method.name());
}

fn collect_assigned_vars(
    method: &cfg::CfgMethod,
    start: usize,
    end: usize,
    predecessors: &HashMap<usize, Vec<usize>>,
) -> Vec<ast::LocalVar> {
    let mut result = Vec::new();
    let mut marked = HashSet::new();
    marked.insert(end);
    marked.insert(start);
    let mut to_visit = vec![start];
    while let Some(current) = to_visit.pop() {
        if let Some(current_predecessors) = predecessors.get(&current) {
            for predecessor in current_predecessors {
                if !marked.contains(predecessor) {
                    to_visit.push(*predecessor);
                    marked.insert(*predecessor);
                }
            }
        }
        check_block(&mut result, &method.basic_blocks[current]);
    }
    result
}

fn check_block(
    vars: &mut Vec<ast::LocalVar>,
    block: &cfg::CfgBlock
) {
    for stmt in &block.stmts {
        match stmt {
            ast::Stmt::MethodCall(_, _, targets) => {
                vars.extend(targets.iter().cloned());
            }
            ast::Stmt::Assign(ast::Expr::Local(var, _), _, _) => {
                vars.push(var.clone());
            }
            _ => {
            }
        }
    }
}

fn add_havoc_stmts(
    method: &mut cfg::CfgMethod,
    head: usize,
    vars: Vec<ast::LocalVar>,
    havoc_methods: &HashMap<ast::TypeId, String>,
) {
    let stmts = &mut method.basic_blocks[head].stmts;
    for var in vars {
        let stmt = ast::Stmt::MethodCall(
            havoc_methods[&var.typ.get_id()].clone(),
            vec![],
            vec![var],
        );
        stmts.push(stmt);
    }
}
