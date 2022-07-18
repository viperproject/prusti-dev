// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    joins::{unify_moves, PCSRepacker},
    syntax::{
        hoare_semantics::HoareSemantics, MicroMirData, MicroMirEncoder, MicroMirStatement,
        MicroMirTerminator, PCSPermission, PCS,
    },
    util::{expand_place, EncodingResult},
};
use prusti_interface::{environment::Environment, PrustiError};
use prusti_rustc_interface::{
    errors::MultiSpan,
    middle::{
        mir::{Body, Mutability, Place},
        ty::TyCtxt,
    },
};

pub fn dump_pcs<'tcx>(env: Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures() {
        println!("id: {:#?}", env.get_unique_item_name(proc_id));
        let current_procedure = env.get_procedure(proc_id);
        let mir = current_procedure.get_mir();
        let micro_mir = MicroMirEncoder::expand_syntax(mir)?;

        let operational_pcs = straight_line_pcs(env.tcx(), &micro_mir);

        // Q: Can we get the MIR?
        // let mir = env.local_mir(proc_id.expect_local(), env.identity_substs(proc_id));
        // println!("{:#?}", *mir);
        // Alternate:

        // Q: What about borrowck facts?
        // if let Some(facts) = env.try_get_local_mir_borrowck_facts(proc_id.expect_local()) {
        //     println!("{:#?}", (*facts).input_facts);
        // } else {
        //     println!("No borrowck facts");
        // }

        // Q: What kind of loop information can we get?
        // let loop_info = current_procedure.loop_info();
        // println!("\theads: {:#?}", loop_info.loop_heads);
        // println!("\thead depths: {:#?}", loop_info.loop_head_depths);

        // Q: MIR analyses?
    }

    return Ok(());
}

pub struct StraitLineOpPCS<'mir> {
    pub micromir: &'mir MicroMirEncoder<'mir>,
    pub statements: Vec<MicroMirStatement<'mir>>, // Replace this with general CGF AST
    pub pcs_before: Vec<PCS<'mir>>,
    pub final_pcs: PCS<'mir>,
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
            MicroMirStatement::Kill(p) => {
                let p_e = PCSPermission::new_initialized(Mutability::Mut, *p);
                let p_u = PCSPermission::new_uninit(*p);

                if current_state.set.contains(&p_e) {
                    Ok(PCS::from_vec(vec![p_e]))
                } else if current_state.set.contains(&p_u) {
                    Ok(PCS::from_vec(vec![p_u]))
                } else {
                    Err(PrustiError::internal(
                        format!("kill elaboration: place {:?} unkillable", p),
                        MultiSpan::new(),
                    ))
                }
            }
            _ => Err(PrustiError::unsupported(
                format!("unsupported elaboration of {:?} precondition", statement),
                MultiSpan::new(),
            )),
        },
    }
}

fn apply_packings<'mir>(
    mut state: PCS<'mir>,
    statements: &mut Vec<MicroMirStatement<'mir>>,
    before_pcs: &mut Vec<PCS<'mir>>,
    packings: PCSRepacker<'mir>,
    tcx: TyCtxt<'mir>,
    mir: &Body<'mir>,
) -> EncodingResult<PCS<'mir>> {
    // TODO: Move insert and remove (guarded with linearity) into PCS
    for p in packings.unpacks.iter() {
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
        let to_regain: Vec<Place<'mir>> = expand_place(*p, mir, tcx)?;
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

    for p in packings.packs.iter().rev() {
        before_pcs.push(state.clone());
        let to_lose: Vec<Place<'mir>> = expand_place(*p, mir, tcx)?;
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

/// Single-pass computation of the PCS for straight-line code
pub fn straight_line_pcs<'mir, 'tcx: 'mir>(
    tcx: TyCtxt<'tcx>,
    micro_mir: &'mir MicroMirEncoder<'mir>,
) -> EncodingResult<StraitLineOpPCS<'mir>>
where
    'mir: 'tcx,
{
    // Is this correct? I think not and either way it's a bad way to get the first block.
    let mut current_block: &MicroMirData<'mir> = micro_mir.get_block(0)?;

    let mut pcs_before: Vec<PCS<'mir>> = Vec::default();
    let mut statements: Vec<MicroMirStatement<'mir>> = Vec::default();

    // Also not correct, read function args
    let mut current_state = PCS::empty();

    loop {
        // Compute PCS for the block
        for statement in current_block.statements.iter() {
            // Elaborate the precondition of the statement
            let next_statement_state = naive_elaboration(&statement, &current_state)?;

            // Go through the packings, apply them and add to encoding.
            let packings =
                unify_moves(&current_state, &next_statement_state, &micro_mir.body, tcx)?;
            current_state = apply_packings(
                current_state,
                &mut statements,
                &mut pcs_before,
                packings,
                tcx,
                &micro_mir.body,
            )?;

            // Push the statement, should be coherent now
            statements.push(statement.clone());
            pcs_before.push(current_state.clone());
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
        micromir: micro_mir,
        statements,
        pcs_before,
        final_pcs: current_state,
    });
}
