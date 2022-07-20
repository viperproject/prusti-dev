// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    joins::{unify_moves, PCSRepacker},
    syntax::{
        hoare_semantics::HoareSemantics, LinearResource, MicroMirData, MicroMirEncoder,
        MicroMirStatement, MicroMirTerminator, PCSPermission, PCS,
    },
    util::EncodingResult,
};
use prusti_interface::{
    environment::{Environment, Procedure},
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::stable_set::FxHashSet,
    errors::MultiSpan,
    middle::mir::{Body, Mutability, Place},
};
use std::iter::zip;

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let micro_mir: MicroMirEncoder<'tcx> = MicroMirEncoder::expand_syntax(mir)?;
        micro_mir.pprint();
        straight_line_pcs(&micro_mir, mir, env)?.pprint();
    }
    Ok(())
}

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
    micro_mir: &'mir MicroMirEncoder<'tcx>,
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
fn naive_elaboration<'tcx>(
    statement: &MicroMirStatement<'tcx>,
    current_state: &PCS<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
    match statement.precondition() {
        Some(s) => Ok(s),
        None => match statement {
            MicroMirStatement::Kill(LinearResource::Mir(p)) => {
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

fn apply_packings<'tcx>(
    mut state: PCS<'tcx>,
    statements: &mut Vec<MicroMirStatement<'tcx>>,
    before_pcs: &mut Vec<PCS<'tcx>>,
    packings: PCSRepacker<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
    // TODO: Move insert and remove (guarded with linearity) into PCS

    for (p, unpacked_p) in packings.unpacks.iter() {
        before_pcs.push(state.clone());

        let to_lose = p.clone();
        // TODO: We're assuming all places are mutably owned right now
        if !state.set.remove(&PCSPermission::new_initialized(
            Mutability::Mut,
            to_lose.into(),
        )) {
            return Err(PrustiError::internal(
                format!("prusti generated an incoherent unpack"),
                MultiSpan::new(),
            ));
        }
        let to_regain: Vec<Place<'tcx>> = unpacked_p.iter().cloned().collect();
        for p1 in to_regain.iter() {
            if !state.set.insert(PCSPermission::new_initialized(
                Mutability::Mut,
                (*p1).into(),
            )) {
                return Err(PrustiError::internal(
                    format!("prusti generated an incoherent unpack"),
                    MultiSpan::new(),
                ));
            }
        }
        statements.push(MicroMirStatement::Unpack(to_lose, to_regain));
    }

    for (p, pre_p) in packings.packs.iter().rev() {
        before_pcs.push(state.clone());

        let to_lose: Vec<Place<'tcx>> = pre_p.iter().cloned().collect(); // expand_place(*p, mir, env)?;
        for p1 in to_lose.iter() {
            if !state.set.remove(&PCSPermission::new_initialized(
                Mutability::Mut,
                (*p1).into(),
            )) {
                return Err(PrustiError::internal(
                    format!("prusti generated an incoherent pack precondition {:?}", p1),
                    MultiSpan::new(),
                ));
            }
        }

        let to_regain = p.clone();

        if !state.set.insert(PCSPermission::new_initialized(
            Mutability::Mut,
            to_regain.into(),
        )) {
            return Err(PrustiError::internal(
                format!(
                    "prusti generated an incoherent pack postcondition: {:?}",
                    to_regain
                ),
                MultiSpan::new(),
            ));
        }

        statements.push(MicroMirStatement::Pack(to_lose, to_regain));
    }
    return Ok(state);
}
