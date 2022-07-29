// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    joins::{apply_packings, unify_moves},
    syntax::{
        hoare_semantics::HoareSemantics, LinearResource, MicroMirData, MicroMirEncoder,
        MicroMirStatement, MicroMirTerminator, PCSPermission, PCS,
    },
    util::EncodingResult,
};
use prusti_interface::{environment::Environment, utils::is_prefix, PrustiError};
use prusti_rustc_interface::{
    data_structures::stable_set::FxHashSet, errors::MultiSpan, middle::mir::Body,
};
use std::iter::zip;

pub struct StraitLineOpPCS<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub pcs_before: Vec<PCS<'tcx>>,
    pub final_pcs: PCS<'tcx>,
}

impl<'tcx> StraitLineOpPCS<'tcx> {
    pub fn pprint(&self) {
        for (st, pcs) in zip(self.statements.iter(), self.pcs_before.iter()) {
            print!("\tPCS: ");
            pcs.pprint_contents();
            println!();
            println!("\t\t{:?}", st);
        }

        print!("\tPCS: ");
        self.final_pcs.pprint_contents();
        println!();
    }
}

/// Single-pass computation of the PCS for straight-line code
///     - naive joins with move-only code
///     - Reduction to a single node (no CFG AST)
///     - Only exclusive and temporary permissions
pub fn straight_line_pcs<'mir, 'env: 'mir, 'tcx: 'env>(
    micro_mir: &'mir MicroMirEncoder<'mir, 'tcx>,
    mir: &'mir Body<'tcx>,
    env: &'env Environment<'tcx>,
) -> EncodingResult<StraitLineOpPCS<'tcx>> {
    // todo: is this always the correct way to find the first block?
    let mut current_block: &MicroMirData<'tcx> = micro_mir.get_block(0)?;
    let mut pcs_before: Vec<PCS<'tcx>> = Vec::default();
    let mut statements: Vec<MicroMirStatement<'tcx>> = Vec::default();
    // todo: read function arguments to get the initial state
    let mut current_state = PCS::empty();

    loop {
        // Compute PCS for the block
        for statement in current_block.statements.iter() {
            // 1. Precondition elaboration
            let next_statement_state = naive_elaboration(&statement, &current_state)?;
            // 2. Unification of the free PCS via packs and unpacks
            let packings = unify_moves(&current_state, &next_statement_state, mir, env)?;
            current_state =
                apply_packings(current_state, &mut statements, &mut pcs_before, packings)?;

            // 3. Statement is now coherent, push
            statements.push(statement.clone());
            pcs_before.push(current_state.clone());

            // 4. Apply statement's hoare semantics
            for p1 in next_statement_state.set.iter() {
                if !current_state.set.remove(p1) {
                    return Err(PrustiError::internal(
                        format!(
                            "generated PCS is incoherent (precondition): {:#?}",
                            next_statement_state.set
                        ),
                        MultiSpan::new(),
                    ));
                }
            }

            let post = match statement.postcondition() {
                Some(s) => s,
                None => {
                    return Err(PrustiError::unsupported(
                        format!("naive elaboration does not support postconditions"),
                        MultiSpan::new(),
                    ))
                }
            };

            for p1 in post.set.iter() {
                if !current_state.set.insert((*p1).clone()) {
                    return Err(PrustiError::internal(
                        format!(
                            "generated PCS is incoherent (postcondition) {:?} in {:?}",
                            p1, current_state
                        ),
                        MultiSpan::new(),
                    ));
                }
            }
        }

        // todo: this doesn't generalize.
        // In the straight line problem, the terminator precondition is always
        // empty since it's always GOTO or JUMP
        match current_block.terminator {
            MicroMirTerminator::Jump(bnext) => {
                // TODO: refactor into CFG representation
                current_block = match micro_mir.encoding.get(&bnext) {
                    Some(s) => s,
                    None => {
                        return Err(PrustiError::internal(
                            "unexpected error when retrieving basic block",
                            MultiSpan::new(),
                        ));
                    }
                }
            }
            MicroMirTerminator::Return(_) => {
                // Log result and break
                // todo: technically has a precondition, see encoding.
                break;
            }
            _ => {
                return Err(PrustiError::unsupported(
                    "only jump and return statements supported",
                    MultiSpan::new(),
                ));
            }
        }
    }

    return Ok(StraitLineOpPCS {
        statements,
        pcs_before,
        final_pcs: current_state.clone(),
    });
}

/// Simplest possible kill-elaboration, can be done
/// in the same pass as pcs computation.
/// { e p } kill p { u p } or
/// { u p } kill p { u p }
pub fn naive_elaboration<'tcx>(
    statement: &MicroMirStatement<'tcx>,
    current_state: &PCS<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
    match statement.precondition() {
        Some(s) => Ok(s),
        None => match statement {
            MicroMirStatement::Kill(_, LinearResource::Mir(p)) => {
                // Remove all places which are a prefix of the statement to kill (p).
                let mut set: FxHashSet<PCSPermission<'tcx>> = FxHashSet::default();
                for current_permission in current_state.set.iter() {
                    if let LinearResource::Mir(p0) = current_permission.target {
                        if is_prefix(p0, (*p).clone()) {
                            set.insert(current_permission.clone());
                        }
                    }
                }
                return Ok(PCS { set });
            }
            _ => Err(PrustiError::unsupported(
                format!("unsupported elaboration of {:?} precondition", statement),
                MultiSpan::new(),
            )),
        },
    }
}
