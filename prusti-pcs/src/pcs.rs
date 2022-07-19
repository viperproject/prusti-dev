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
use analysis::mir_utils::{expand_one_level, PlaceImpl};
use prusti_interface::{
    environment::{Environment, Procedure},
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::{stable_map::FxHashMap, stable_set::FxHashSet},
    errors::MultiSpan,
    middle::{
        mir::{Body, Mutability, Place},
        ty::TyCtxt,
    },
};

pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &Body<'tcx> = current_procedure.get_mir();
        let micro_mir: MicroMirEncoder<'tcx> = MicroMirEncoder::expand_syntax(mir)?;
        micro_mir.pprint();
        let operational_pcs = straight_line_pcs(&micro_mir, mir, env)?;

        print!("\tPCS: ");
        for s in operational_pcs.initial_pcs.set.iter() {
            print!("{:#?}, ", s)
        }
        println!();

        let mut i = 0;
        while i < operational_pcs.statements.len() {
            // Report PCS before

            println!("\t\t{:?}", operational_pcs.statements[i]);

            print!("\tPCS: ");
            for s in operational_pcs.pcs_after[i].set.iter() {
                print!("{:#?}, ", s)
            }
            println!();

            i += 1;
        }
    }
    Ok(())
}

pub struct StraitLineOpPCS<'tcx> {
    pub statements: Vec<MicroMirStatement<'tcx>>,
    pub pcs_after: Vec<PCS<'tcx>>,
    pub initial_pcs: PCS<'tcx>,
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
    // Is this correct? I think not and either way it's a bad way to get the first block.
    let mut current_block: &MicroMirData<'tcx> = micro_mir.get_block(0)?;

    let mut pcs_after: Vec<PCS<'tcx>> = Vec::default();
    let mut statements: Vec<MicroMirStatement<'tcx>> = Vec::default();

    // Also not correct, read function args
    let mut current_state = PCS::empty();
    let initial_pcs = current_state.clone();

    loop {
        // Compute PCS for the block
        for statement in current_block.statements.iter() {
            // println!("  working on {:?} ", statement);
            // Elaborate the precondition of the statement
            let next_statement_state = naive_elaboration(&statement, &current_state)?;
            // println!(
            //     "      attempt to unify: {:#?} and {:#?}",
            //     current_state, next_statement_state
            // );
            // Go through the packings, apply them and add to encoding.
            let packings = unify_moves(&current_state, &next_statement_state, mir, env)?;
            current_state = apply_packings(
                current_state,
                &mut statements,
                &mut pcs_after,
                packings,
                mir,
                env,
            )?;

            // Now apply the statement's hoare triple
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
                        format!("generated PCS is incoherent (postcondition) {:?}", p1),
                        MultiSpan::new(),
                    ));
                }
            }

            // Push the statement, should be coherent now
            statements.push(statement.clone());
            pcs_after.push(current_state.clone());
        }

        // In the straight line problem, the terminator precondition is always
        // empty since it's always GOTO or JUMP. => do not compute this special case here

        // if JUMP
        //      => Contiunue verifiaction on jumped-to block
        match current_block.terminator {
            MicroMirTerminator::Jump(bnext) => {
                // TODO: refactor into micro_mir implementation
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

    // Report
    //  interp. final PCS *before* return, so the return statement is not computed
    //   (some aspects of the theory still to work out here)

    return Ok(StraitLineOpPCS {
        statements,
        pcs_after,
        initial_pcs,
    });
}

// Simplest possible kill-elaboration, can be done
// in the same pass as pcs computation.
// { e p } kill p { u p } or
// { u p } kill p { u p }
fn naive_elaboration<'tcx>(
    statement: &MicroMirStatement<'tcx>,
    current_state: &PCS<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
    match statement.precondition() {
        Some(s) => Ok(s),
        None => match statement {
            MicroMirStatement::Kill(LinearResource::Mir(p)) => {
                // Naive kill elaboration will remove all places which are a prefix of the statement to kill (p).
                let mut set: FxHashSet<PCSPermission<'tcx>> = FxHashSet::default();

                return Ok(PCS { set });
                // let p_e = PCSPermission::new_initialized(Mutability::Mut, *p);
                // let p_u = PCSPermission::new_uninit(*p);

                // if current_state.set.contains(&p_e) {
                //     Ok(PCS::from_vec(vec![p_e]))
                // } else if current_state.set.contains(&p_u) {
                //     Ok(PCS::from_vec(vec![p_u]))
                // } else {
                //     Err(PrustiError::internal(
                //         format!(
                //             "kill elaboration: place {:?} unkillable in the current PCS {:#?}",
                //             p, current_state.set
                //         ),
                //         MultiSpan::new(),
                //     ))
                // }
            }
            _ => Err(PrustiError::unsupported(
                format!("unsupported elaboration of {:?} precondition", statement),
                MultiSpan::new(),
            )),
        },
    }
}

fn apply_packings<'mir, 'env: 'mir, 'tcx: 'env>(
    mut state: PCS<'tcx>,
    statements: &mut Vec<MicroMirStatement<'tcx>>,
    before_pcs: &mut Vec<PCS<'tcx>>,
    packings: PCSRepacker<'tcx>,
    mir: &'mir Body<'tcx>,
    env: &'env Environment<'tcx>,
    // tcx: TyCtxt<'mir>,
    // mir: &Body<'mir>,
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
        let mut to_lose: Vec<Place<'tcx>> = pre_p.iter().cloned().collect(); // expand_place(*p, mir, env)?;
        for p1 in to_lose.iter() {
            if !state.set.remove(&PCSPermission::new_initialized(
                Mutability::Mut,
                (*p1).into(),
            )) {
                return Err(PrustiError::internal(
                    format!("prusti generated an incoherent pack"),
                    MultiSpan::new(),
                ));
            }
        }

        let to_regain = p.clone();

        if !state.set.remove(&PCSPermission::new_initialized(
            Mutability::Mut,
            to_regain.into(),
        )) {
            return Err(PrustiError::internal(
                format!("prusti generated an incoherent pack"),
                MultiSpan::new(),
            ));
        }

        statements.push(MicroMirStatement::Pack(to_lose, to_regain));
    }
    return Ok(state);
}
