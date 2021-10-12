// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic as vir;
use rustc_middle::mir;
use std::collections::HashMap;
use std::fmt::{self, Debug, Display};
use std::iter::FromIterator;
use std::marker::Sized;
use log::trace;
use std::mem;
use crate::encoder::errors::EncodingError;

/// Backward interpreter for a loop-less MIR
pub trait BackwardMirInterpreter<'tcx> {
    type Error: Sized;
    type State: Sized;
    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        terminator: &mir::Terminator<'tcx>,
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error>;
    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error>;
}

/// Interpret a loop-less MIR starting from the end and return the **initial** state.
/// The result is None if the CFG contains a loop.
pub fn run_backward_interpretation<'tcx, S, E, I>(
    mir: &mir::Body<'tcx>,
    interpreter: &I,
) -> Result<Option<S>, E> where
    S: Debug,
    E: Debug,
    I: BackwardMirInterpreter<'tcx, State = S, Error = E>
{
    let basic_blocks = mir.basic_blocks();
    let mut heads: HashMap<mir::BasicBlock, S> = HashMap::new();

    // Find the final basic blocks
    let mut pending_blocks: Vec<mir::BasicBlock> = basic_blocks
        .iter_enumerated()
        .filter(|(_, bb_data)| match bb_data.terminator {
            Some(ref term) => term.successors().next().is_none(),
            _ => false,
        })
        .map(|(bb, _)| bb)
        .collect();

    // Interpret all the blocks in `pending_blocks`
    while !pending_blocks.is_empty() {
        let curr_bb = pending_blocks.pop().unwrap();
        let bb_data = &basic_blocks[curr_bb];

        // Apply the terminator
        let terminator = bb_data.terminator();
        let states = HashMap::from_iter(terminator.successors().map(|bb| (*bb, &heads[bb])));
        trace!("States before: {:?}", states);
        trace!("Apply terminator {:?}", terminator);
        let mut curr_state = interpreter.apply_terminator(curr_bb, terminator, states)?;
        trace!("State after: {:?}", curr_state);

        // Apply each statement, from the last
        for (stmt_index, stmt) in bb_data.statements.iter().enumerate().rev() {
            trace!("State before: {:?}", curr_state);
            trace!("Apply statement {:?}", stmt);
            interpreter.apply_statement(curr_bb, stmt_index, stmt, &mut curr_state)?;
            trace!("State after: {:?}", curr_state);
        }

        // Store the state at the beginning of block `curr_bb`
        heads.insert(curr_bb, curr_state);

        // Put the preceding basic blocks
        for &pred_bb in mir.predecessors()[curr_bb].iter() {
            if let Some(ref term) = basic_blocks[pred_bb].terminator {
                if term.successors().all(|succ_bb| heads.contains_key(succ_bb)) {
                    pending_blocks.push(pred_bb);
                }
            }
        }
    }

    let result = heads.remove(&basic_blocks.indices().next().unwrap());

    if result.is_none() {
        trace!("heads: {:?}", heads);
    }

    Ok(result)
}

/// Interpret a loop-less MIR starting from the end and return the **initial** state.
/// The result is None if the CFG contains a loop.
pub fn run_backward_interpretation_point_to_point<
    'tcx,
    S: Debug + Clone,
    E,
    I: BackwardMirInterpreter<'tcx, State = S, Error = E>,
>(
    mir: &mir::Body<'tcx>,
    interpreter: &I,
    initial_bbi: mir::BasicBlock,
    final_bbi: mir::BasicBlock,
    final_stmt_index: usize,
    final_state: S,
    undef_state: S,
) -> Result<Option<S>, E> {
    let basic_blocks = mir.basic_blocks();
    let mut heads: HashMap<mir::BasicBlock, S> = HashMap::new();
    trace!(
        "[start] run_backward_interpretation_point_to_point:\n - from final block {:?}, statement {}\n - and state {:?}\n - to initial block {:?}\n - using undef state {:?}",
        final_bbi,
        final_stmt_index,
        final_state,
        initial_bbi,
        undef_state,
    );

    // Find the final basic blocks
    let mut pending_blocks: Vec<mir::BasicBlock> = vec![final_bbi];

    // Interpret all the blocks in `pending_blocks`
    while !pending_blocks.is_empty() {
        let curr_bb = pending_blocks.pop().unwrap();
        let bb_data = &basic_blocks[curr_bb];
        trace!("curr_bb: {:?}", curr_bb);

        // Apply the terminator
        let terminator = bb_data.terminator();
        let terminator_index = bb_data.statements.len();
        let states = {
            // HACK: when a successor is undefined, clone the first defined successor.
            // This happens for example when Prusti skips the encoding of a cleanup CFG edge.
            let default_state = terminator
                .successors()
                .flat_map(|bb| heads.get(bb))
                .next()
                .unwrap_or(&undef_state);
            HashMap::from_iter(
                terminator
                    .successors()
                    .map(|bb| (*bb, heads.get(bb).unwrap_or(default_state))),
            )
        };
        trace!("States before: {:?}", states);
        debug_assert_eq!(states.len(), terminator.successors().count());
        trace!("Apply terminator {:?}", terminator);
        let mut curr_state = interpreter.apply_terminator(
            curr_bb,
            terminator,
            states
        )?;
        trace!("State after: {:?}", curr_state);
        if curr_bb == final_bbi && final_stmt_index == terminator_index {
            trace!("Final location reached in terminator");
            curr_state = final_state.clone();
            trace!("State after: {:?}", curr_state);
        }

        // Apply each statement, from the last
        for (stmt_index, stmt) in bb_data.statements.iter().enumerate().rev() {
            trace!("State before: {:?}", curr_state);
            trace!("Apply statement {:?}", stmt);
            interpreter.apply_statement(curr_bb, stmt_index, stmt, &mut curr_state)?;
            trace!("State after: {:?}", curr_state);
            if curr_bb == final_bbi && final_stmt_index == stmt_index {
                trace!("Final location reached in statement");
                curr_state = final_state.clone();
                trace!("State after: {:?}", curr_state);
            }
        }

        // Store the state at the beginning of block `curr_bb`
        heads.insert(curr_bb, curr_state);

        if curr_bb != initial_bbi {
            // Put the preceding basic blocks
            for &pred_bb in mir.predecessors()[curr_bb].iter() {
                // Note: here we don't check that all the successors of `pred_bb` has been visited.
                // It's a known limitation, because this is the point-to-point interpretation.
                // Use `run_backward_interpretation` if the check is important.
                pending_blocks.push(pred_bb);
            }
        }
    }

    let result = heads.remove(&initial_bbi);

    if result.is_none() {
        trace!("heads: {:?}", heads);
    }

    trace!(
        "[end] run_backward_interpretation_point_to_point:\n - from final final block {:?}, statement {}\n - and state {:?}\n - to initial block {:?}\n - using undef state {:?}\n - resulted in state {:?}",
        final_bbi,
        final_stmt_index,
        final_state,
        initial_bbi,
        undef_state,
        result
    );

    Ok(result)
}

#[derive(Clone, Debug)]
pub struct ExprBackwardInterpreterState {
    /// None if the expression is undefined.
    expr: Option<vir::Expr>,
    substs: HashMap<vir::TypeVar, vir::Type>,
}

impl Display for ExprBackwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(expr) = self.expr.as_ref() {
            write!(f, "expr={}", expr)
        } else {
            write!(f, "expr=undefined")
        }
    }
}

impl ExprBackwardInterpreterState {
    pub fn new(expr: Option<vir::Expr>) -> Self {
        ExprBackwardInterpreterState { expr, substs: HashMap::new() }
    }

    pub fn new_defined(expr: vir::Expr) -> Self {
        ExprBackwardInterpreterState { expr: Some(expr), substs: HashMap::new() }
    }

    pub fn new_undefined() -> Self {
        ExprBackwardInterpreterState { expr: None, substs: HashMap::new() }
    }

    pub fn new_defined_with_substs(
        expr: vir::Expr,
        substs: HashMap<vir::TypeVar, vir::Type>,
    ) -> Self {
        ExprBackwardInterpreterState { expr: Some(expr), substs }
    }

    pub fn expr(&self) -> Option<&vir::Expr> {
        self.expr.as_ref()
    }

    pub fn expr_mut(&mut self) -> Option<&mut vir::Expr> {
        self.expr.as_mut()
    }

    pub fn into_expr(self) -> Option<vir::Expr> {
        self.expr
    }

    pub fn substitute_value(&mut self, target: &vir::Expr, replacement: vir::Expr) {
        trace!("substitute_value {:?} --> {:?}", target, replacement);
        let target = target.clone().patch_types(&self.substs);
        let replacement = replacement.patch_types(&self.substs);

        if let Some(curr_expr) = self.expr.as_mut() {
            // Replace two times to avoid cloning `expr`, which could be big.
            let expr = mem::replace(curr_expr, true.into());
            let new_expr = expr.replace_place(&target, &replacement).simplify_addr_of();
            let _ = mem::replace(curr_expr, new_expr);
        }
    }

    pub fn uses_place(&self, sub_target: &vir::Expr) -> bool {
        trace!("use_place {:?}", sub_target);
        let sub_target = sub_target.clone().patch_types(&self.substs);
        self.expr.as_ref().map(|expr| expr.find(&sub_target)).unwrap_or(false)
    }
}
