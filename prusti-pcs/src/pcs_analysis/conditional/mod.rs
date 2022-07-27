// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused_imports)]
use crate::{
    joins::{apply_packings, unify_moves},
    syntax::{
        hoare_semantics::HoareSemantics, LinearResource, MicroMirData, MicroMirEncoder,
        MicroMirEncoding, MicroMirStatement, MicroMirTerminator, PCSPermission, PCS,
    },
    util::EncodingResult,
};
use prusti_interface::{
    environment::{
        mir_analyses::{
            allocation::DefinitelyAllocatedAnalysisResult,
            initialization::DefinitelyInitializedAnalysisResult,
        },
        Environment,
    },
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    middle::mir::{BasicBlock, Body},
};
use std::iter::zip;

/// Result of a CondPCS procedure
pub struct CondPCSBlock<'tcx> {
    statements: Vec<MicroMirStatement<'tcx>>,
    pcs_before: FxHashMap<BasicBlock, Vec<PCS<'tcx>>>,
    terminator: MicroMirTerminator<'tcx>,
    pcs_after_terminator: Vec<PCS<'tcx>>,
}

/// Result of a CondPCS procedure
pub struct CondPCS<'tcx> {
    pub blocks: FxHashMap<BasicBlock, CondPCSBlock<'tcx>>,
}

/// Collection of all information needed to compute the CondPCS
/// statically computed beforehand (input facts)
pub struct CondPCSctx<'mir, 'env: 'mir, 'tcx: 'env> {
    pub micro_mir: &'mir MicroMirEncoding<'tcx>,
    pub mir: &'mir Body<'tcx>,
    pub env: &'env Environment<'tcx>,
    pub init_analysis: DefinitelyInitializedAnalysisResult<'tcx>,
    pub alloc_analysis: DefinitelyAllocatedAnalysisResult,
}

/// Pointwise state during generation (transient)
pub struct CondPCSstate<'tcx> {
    bb: BasicBlock,
    pcs: PCS<'tcx>,
}

/// Computation of a PCS including conditionals
///     Does not currently track conditionally flagged information needed
///     for the viper encoding, just the PCS.
///
/// INVARIANT: Free PCS is a subset of the Definitely Initialized places
pub fn cond_pcs<'mir, 'env, 'tcx>(
    ctx: CondPCSctx<'mir, 'env, 'tcx>,
) -> EncodingResult<CondPCS<'tcx>> {
    // todo: get this info from the compiler in the proper way
    let mut initial_state = CondPCSstate {
        bb: (0 as u32).into(),
        pcs: PCS::empty(),
    };

    // Iterate through the graph. Simple rule for all possible join points:
    //    We will not store the weakened data right now,  just replace
    //      e x -> u x and u x -> nothing. In the future it
    //      must be stored in an auxiliarry data structure for defered drops.
    // Note that: loops can only weaken the permissions. It's not possible for
    //  a not-owned place to become owned in the loop. AFAICT The initial
    //  permissions are an upper bound on the permissions at any loop iteration
    //  on the lattice interpretation of places (is this true? formalize me!)
    // Wait... is it just a bound or is it a characterization?
    // INIT x => ALLOC x
    // INIT x <=> e x
    // ALLOC x & !INIT x <=> u x
    let mut dirty_blocks: Vec<CondPCSstate> = vec![initial_state];
    while let Some(current_block) = dirty_blocks.pop() {
        let mut pcs_before: Vec<PCS<'tcx>> = vec![];
        // Load up current block
        let mut pcs = current_block.pcs;
        // Check that the PCS is coherent with the initialization analysis,
        //  and if not, trim.
        // Might this lead to packs and unpacks??? yes (damn!)
        // However, most terminators have no preconditions, so it's sound to push these
        // back through the terminator (ie. compute the packs/unpacks for the destination
        // when computing the jumped-from block).
        // Note that some terminators don't do this, like return or function calls.
        // We'll have to handle these separately, maybe even introducing ghost blocks.
        let _permission_leaks = trim_pcs(&mut pcs, &(ctx.init_analysis), &(ctx.alloc_analysis));

        // For each statement...
        let block_data = ctx.micro_mir.get(&current_block.bb).ok_or(
            return Err(PrustiError::internal(
                "basic block out of bounds",
                MultiSpan::new(),
            )),
        )?;
        for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
            // Elaborate the precondition for the next statement
            // Unify the current PCS with the PCS for the next statement
            // Push the unificiation glue
            // Push the statement
            // Apply the Hoare triple for the statement's semantics
        }
        // Elaborate the precondition for the terminator
        // Unify the current PCS with the PCS for the terminator
        // Push the unification glue to statements
        // Push the terminator
        // Apply the Hoare triple for the terminator's semantics
        // Set final PCS from current PCS
        // Push the next blocks with their respective states
    }

    todo!();
}

/// Modifies a PCS to be coherent with the initialization state, and returns permissions
/// to weaken
pub fn trim_pcs<'tcx>(
    pcs: &mut PCS<'tcx>,
    init_analysis: &DefinitelyInitializedAnalysisResult<'tcx>,
    alloc_analysis: &DefinitelyAllocatedAnalysisResult,
) -> PCS<'tcx> {
    todo!();
}

// Note: Always repack on outgoing edges.
//
// PCS A -- repacks --.
//                   join = PCS C
// PCS B -- repacks --'
//
// as opposed to
//
// PCS A ----.
//          join -- repacks --> PCS C
// PCS B ----'
//
// as every unification done by the latter can be done by the former,
//  but not vice-versa.
