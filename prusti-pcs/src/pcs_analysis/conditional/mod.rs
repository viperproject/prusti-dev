// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused_imports)]
use crate::{
    joins::{apply_packings, unify_moves, RepackPackup},
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
use std::iter::{repeat, zip};

/// Straight line micromir
/// Invariant:
pub struct MicroMirSequence<'tcx> {
    statements: Vec<MicroMirStatement<'tcx>>,
    pcs_before: Vec<PCS<'tcx>>,
}

/// Result of a CondPCS procedure
/// INVARIANT: len(statements) == len(pcs_before)
pub struct CondPCSBlock<'tcx> {
    statements: Vec<MicroMirStatement<'tcx>>,
    pcs_before: Vec<PCS<'tcx>>,
    terminator: MicroMirTerminator<'tcx>,
    pcs_after_terminator: Vec<(BasicBlock, PCS<'tcx>)>,
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

/// Computation of the CondPCS is performed inside a context
impl<'mir, 'env: 'mir, 'tcx: 'env> CondPCSctx<'mir, 'env, 'tcx> {
    /// Computation of a PCS including conditionals
    ///     Does not currently track conditionally flagged information needed
    ///     for the viper encoding, just the PCS.
    ///
    /// INVARIANT: Free PCS is a subset of the Definitely Initialized places
    pub fn cond_pcs(&self) -> EncodingResult<CondPCS<'tcx>> {
        let ret = CondPCS {
            blocks: FxHashMap::default(),
        };

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
            let mut working_pcs_before: Vec<PCS<'tcx>> = vec![];
            let mut working_statements: Vec<MicroMirStatement<'tcx>> = vec![];

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
            let _too_eager_permission_drops = self.trim_pcs(&mut pcs);

            // For each statement...
            let block_data = self
                .micro_mir
                .get(&current_block.bb)
                .ok_or(PrustiError::internal(
                    "basic block out of bounds",
                    MultiSpan::new(),
                ))?;

            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                // Elaborate the precondition for the next statement
                let next_precondition = self.elaborate_precondition(&stmt);
                let next_postcondition = stmt.postcondition().ok_or(PrustiError::unsupported(
                    "postcondition elaboration not supported",
                    MultiSpan::new(),
                ))?;
                // Unify the current PCS with the PCS for the next statement
                // Push the unificiation glue
                let _ = self.repack(&pcs, &next_precondition)?;

                // Push the statement and the current PCS
                working_pcs_before.push(pcs.clone());
                working_statements.push((*stmt).clone());

                // Apply the Hoare triple for the statement's semantics
                let _ = transform_pcs(&mut pcs, &next_precondition, &next_postcondition)?;
            }

            let terminator: MicroMirTerminator<'tcx> = todo!();

            // Elaborate the precondition for the terminator (nothing to elaborate)
            let terminator_precondition =
                terminator.precondition().ok_or(PrustiError::unsupported(
                    "terminator precondition elaboration not supported",
                    MultiSpan::new(),
                ))?;

            let terminator_postcondition =
                terminator.postcondition().ok_or(PrustiError::unsupported(
                    "terminator postcondition elaboration not supported",
                    MultiSpan::new(),
                ))?;

            // Unify the current PCS with the PCS for the terminator
            // Push the unification glue
            let _ = self.repack(&pcs, &terminator_precondition)?;

            // Apply the Hoare triple for the terminator's semantics
            //  for each possible postcondition (there's a vector of them)
            let applied_postconditions: Vec<(BasicBlock, PCS<'tcx>)> = vec![];
            for (bb_next, post) in terminator_postcondition.iter() {
                let pcs1 = pcs.clone();
                transform_pcs(&mut pcs1, &terminator_precondition, post);
                applied_postconditions.push((*bb_next, pcs1));

                // Pack up the PCS as much as possible
                let packup = RepackPackup::new(self.env.tcx(), self.mir, pcs)?;
                for (pre_pack, post_pack) in packup.packs {
                    working_pcs_before.push(pcs);
                    working_statements.push(MicroMirStatement::Pack(
                        pre_pack.into_iter().collect(),
                        post_pack,
                    ))
                }

                // Trim
                todo!();
            }

            // Set final PCS from current PCS
            // Push the next blocks with their respective states
            todo!();

            // Push the fully completed block
            let _ = ret
                .blocks
                .insert(
                    current_block.bb,
                    CondPCSBlock {
                        statements: working_statements,
                        pcs_before: working_pcs_before,
                        terminator: todo!(),                          //
                        pcs_after_terminator: applied_postconditions, // Postconditions
                    },
                )
                .ok_or(PrustiError::internal(
                    "attempt to compute a block twice",
                    MultiSpan::new(),
                ));
        }

        todo!();
    }

    /// Modifies a PCS to be coherent with the initialization state, and returns permissions
    /// to weaken
    fn trim_pcs(&self, pcs: &mut PCS<'tcx>) -> PCS<'tcx> {
        todo!();
    }

    /// Elaborate the precondition of a statement
    fn elaborate_precondition(&self, stmt: &'mir MicroMirStatement<'tcx>) -> PCS<'tcx> {
        // 1. collect the precondition from it's hoare semantics
        // 2. if the precondition is None
        //     2.1. if the statement is a kill of a (MIR) place p
        //              INIT p  => return { e p }
        //              ALLOC p => return { u p }
        //              neither => in principle, this never happens.
        //     2.2. no other statements have undetermined preconditions in this model
        //              return precondition
        todo!();
    }

    /// Computes the unification between two PCS's, inserts packs and repacks as necessary
    fn repack(&self, current_pcs: &PCS<'tcx>, next_pre: &PCS<'tcx>) -> EncodingResult<()> {
        let repacking = unify_moves(current_pcs, next_pre, self.mir, self.env)?;
        todo!();
    }

    // Note:
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

    // Actually! We're doing a different strategy.
    //
    // PCS A -- packs -- trim --.
    //                         join -- unpacks --> PCS C
    // PCS B -- packs -- trim --'
    //
    // - Theorem: All unifiable PCS's can be unified by doing packs, then unpacks
    //  (no interleaving necessary). That is, there is a meet-semilattice of permissions
    //
    // The trimming join enforces the following:
    //      - All exclusive permissions are exactly = init (alloc is a subset of init)
    //      - All uninit permissions are exactly = (init - alloc)
    //
}

/// TODO: Refactor this out from this file.
fn transform_pcs<'tcx>(
    pcs: &mut PCS<'tcx>,
    pre: &PCS<'tcx>,
    post: &PCS<'tcx>,
) -> EncodingResult<()> {
    for p in pre.set.iter() {
        if !pcs.set.remove(p) {
            return Err(PrustiError::internal(
                format!("incoherent precondition: {:#?} in {:#?}", p, pcs.set),
                MultiSpan::new(),
            ));
        }
    }

    for p in pre.set.iter() {
        if !pcs.set.insert((*p).clone()) {
            return Err(PrustiError::internal(
                format!("incoherent postcondition: {:#?} in {:#?}", p, pcs.set),
                MultiSpan::new(),
            ));
        }
    }

    return Ok(());
}
