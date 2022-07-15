// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    syntax::{
        hoare_semantics::HoareSemantics, MicroMirEncoder, MicroMirStatement, PCSPermission, PCS,
    },
    util::EncodingResult,
};
use prusti_interface::{environment::Environment, PrustiError};
use prusti_rustc_interface::{
    errors::MultiSpan,
    middle::{
        mir::{Body, Mutability},
        ty::TyCtxt,
    },
};

pub fn dump_pcs<'tcx>(env: Environment<'tcx>) {
    for proc_id in env.get_annotated_procedures() {
        println!("id: {:#?}", env.get_unique_item_name(proc_id));
        let current_procedure = env.get_procedure(proc_id);
        let _mir = current_procedure.get_mir();

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
}

/// Single-pass computation of the PCS for straight-line code
pub fn straight_line_pcs<'mir, 'tcx: 'mir>(
    mir: &'mir Body<'mir>,
    tcx: TyCtxt<'tcx>,
) -> EncodingResult<()> {
    let micro_mir: MicroMirEncoder<'mir> = MicroMirEncoder::expand_syntax(mir)?;

    // Is this correct? I think not and either way it's bad
    let mut current_block = match micro_mir.encoding.get(&(0 as u32).into()) {
        Some(s) => s,
        None => {
            return Err(PrustiError::internal(
                "unexpected error when retrieving basic block 0",
                MultiSpan::new(),
            ));
        }
    };

    // Also not correct, read function args
    let mut current_state = PCS::empty();

    loop {
        // repack across every statement in the block
        let mut next_s_index = 0;
        loop {
            let mut maybe_next_precondition: PCS<'mir>;
            // Check to see if the next statement is a terminator... if so grab it's precondition
            // Otherwise grab the normal precondition of the next statement.

            // If the next precondition is none, try to elaborate it.

            let mut next_precondition: PCS<'mir>;
            match todo!() {
                Some(pre) => {
                    next_precondition = pre;
                }
                None => {
                    // Simplest possible kill-elaboration, can be done
                    // in the same pass as pcs computation.
                    // { e p } kill p { u p } or
                    // { u p } kill p { u p }
                    //  depending on current PCS.
                    if let MicroMirStatement::Kill(p) = todo!() {
                        let mut_p = PCSPermission::new_initialized(Mutability::Mut, p);
                        let uninit_p = PCSPermission::new_uninit(p);
                        if current_state.set.contains(&mut_p) {
                            next_precondition = PCS::from_vec(vec![mut_p]);
                        } else if current_state.set.contains(&uninit_p) {
                            next_precondition = PCS::from_vec(vec![uninit_p]);
                        } else {
                            return Err(PrustiError::internal(
                                format!("kill elaboration: place {:?} unkillable", p),
                                MultiSpan::new(),
                            ));
                        }
                    } else {
                        return Err(PrustiError::unsupported(
                            format!("unsupported elaboration of {:?} precondition", todo!()),
                            MultiSpan::new(),
                        ));
                    }
                }
            };

            // If we aren't immediately compatible with the next precondition, make it so with packs/unpacks

            if !current_state.set.is_subset(&next_precondition.set) {
                // Try to repack
                // let move_repacker =
                //     unify_moves(current_state.set, next_precondition.set, mir, tcx)?;
                // for stmt in encode()
                // Add the packs and unpacks into the program
                // Update the next_precondition to be the first packs's precondition
            }

            // Transfer: remove preconditions and add postconditions

            next_s_index += 1;
        }

        // Advance to the next block or error if not straight-line verification

        break;
    }

    // Report
    todo!();
}

/// Pointwise state for the analysis
struct PCSState<'tcx> {
    pcs: PCS<'tcx>,
}
