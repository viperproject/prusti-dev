// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![allow(unused_imports)]
use crate::{
    joins::{RepackPackup, RepackUnify},
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
    middle::mir::{BasicBlock, Body, Location, Mutability, Place},
};
use std::iter::{repeat, zip};
use syn::__private::quote::__private::LineColumn;

/// Straight line, fully elaborated MicroMir
/// INVARIANT: coherent pre- and post- conditions
/// INVARIANT: len(statements) == len(pcs_before)
pub struct StraightOperationalMir<'tcx> {
    statements: Vec<MicroMirStatement<'tcx>>,
    pcs_before: Vec<PCS<'tcx>>,
}

impl<'tcx> Default for StraightOperationalMir<'tcx> {
    fn default() -> StraightOperationalMir<'tcx> {
        StraightOperationalMir {
            statements: vec![],
            pcs_before: vec![],
        }
    }
}

/// OperationalMIR which lives on CFG edges,
/// Does not correspond to any MIR location
pub struct PostBlock<'tcx> {
    body: StraightOperationalMir<'tcx>,
    next: BasicBlock,
}

/// Result of a CondPCS procedure
pub struct CondPCSBlock<'tcx> {
    body: StraightOperationalMir<'tcx>,
    terminator: MicroMirTerminator<'tcx>,
    pcs_after: Vec<(PostBlock<'tcx>, PCS<'tcx>)>,
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

/// Data structure for all computations of the CondPCS
impl<'mir, 'env: 'mir, 'tcx: 'env> CondPCSctx<'mir, 'env, 'tcx> {
    pub fn cond_pcs(&self) -> EncodingResult<CondPCS<'tcx>> {
        // Map of blocks and their Operational PCS's
        let mut generated_blocks: FxHashMap<BasicBlock, CondPCSBlock<'tcx>> = FxHashMap::default();

        // Computation left to do
        let mut dirty_blocks = self.initial_state();

        while let Some((mut bb, mut pcs)) = dirty_blocks.pop() {
            // Translate the basic block bb, starting with PCS pcs
            //  (this should be the exact PCS that all in-edges end up with)
            let block_data = self.get_block_data(&bb)?;
            let mut body = StraightOperationalMir::default();
            pcs = self.translate_body(block_data, &mut body, pcs)?;

            // Repack to apply the terminaor PCS
            let terminator = &block_data.terminator;
            pcs = self.repack(pcs, &terminator.precondition(), &mut body)?;

            let mut pcs_after: Vec<(PostBlock<'tcx>, PCS<'tcx>)> = Vec::default();

            for (next_block, dependent_postcondition) in terminator.postcondition() {
                //      Apply the semantics (we are now joinable mod repacks)
                let mut this_pcs = transform_pcs(
                    pcs.clone(),
                    &terminator.precondition(),
                    &dependent_postcondition,
                )?;

                // Trim the PCS by way of eager drops (we are now the same mod repacks)
                this_pcs = self.trim_pcs(this_pcs, next_block);

                // Pack to the most packed state possible (we are now identical)
                // (any unique state works)
                let mut this_op_mir = StraightOperationalMir::default();
                this_pcs = self.packup(this_pcs, &mut this_op_mir)?;

                // If the next block is not already done, add it as a dirty block (to do)
                if let Some(done_block) = generated_blocks.get(&next_block) {
                    // Check that the final PCS is the same as the
                    // intial PCS in the block
                    if this_pcs != done_block.body.pcs_before[0] {
                        return Err(PrustiError::internal(
                            "trimmed+packed pcs does not match exiting a join",
                            MultiSpan::new(),
                        ));
                    }
                } else if let Some(todo_pcs) = dirty_blocks
                    .iter()
                    .filter_map(|(todo_bb, todo_pcs)| {
                        if *todo_bb == next_block {
                            Some(todo_pcs)
                        } else {
                            None
                        }
                    })
                    .next()
                {
                    // Check that the final PCS is the same as the
                    // intial PCS in the block
                    if this_pcs != *todo_pcs {
                        return Err(PrustiError::internal(
                            "trimmed+packed pcs does not join with a dirty PCS",
                            MultiSpan::new(),
                        ));
                    }
                } else {
                    // Mark the next block as dirty
                    dirty_blocks.push((next_block, this_pcs.clone()));
                }

                pcs_after.push((
                    PostBlock {
                        body: this_op_mir,
                        next: next_block,
                    },
                    this_pcs,
                ));
            }

            generated_blocks.insert(
                block_data.mir_block,
                CondPCSBlock {
                    body,
                    terminator: (*terminator).clone(),
                    pcs_after,
                },
            );
        }

        Ok(CondPCS {
            blocks: generated_blocks,
        })
    }

    // Straight-line PCS computation inside the body of a basic block
    fn translate_body(
        &self,
        block_data: &MicroMirData<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
        mut pcs: PCS<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            // 1. Elaborate the state-dependent conditions
            let location = Location {
                block: block_data.mir_block,
                statement_index: block_data.mir_parent[statement_index],
            };
            let statement_precondition = self.elaborate_precondition(statement, location)?;
            let statement_postcondition = self.elaborate_postcondition(statement)?;

            // 2. Repack to precondition
            pcs = self.repack(pcs, &statement_precondition, op_mir)?;

            // 3. Statement is coherent: push
            op_mir.statements.push(statement.clone());
            op_mir.pcs_before.push(pcs.clone());

            // 4. Apply statement's semantics to state.
            pcs = transform_pcs(pcs, &statement_precondition, &statement_postcondition)?;
        }

        Ok(pcs)
    }

    fn get_block_data(&self, bb: &BasicBlock) -> EncodingResult<&MicroMirData<'tcx>> {
        self.micro_mir.get(bb).ok_or(PrustiError::internal(
            "basic block out of bounds",
            MultiSpan::new(),
        ))
    }

    /// TODO
    ///   1. I do not know if bb0 is always the initial basic block
    ///   2. I certainly know that we do not always start with an empty PCS
    fn initial_state(&self) -> Vec<(BasicBlock, PCS<'tcx>)> {
        vec![((0 as u32).into(), PCS::empty())]
    }

    /// Modifies a PCS to be coherent with the initialization state, and returns permissions
    /// to weaken
    fn trim_pcs(&self, mut pcs: PCS<'tcx>, block: BasicBlock) -> PCS<'tcx> {
        todo!();
    }

    /// Elaborate the precondition of a statement
    fn elaborate_precondition(
        &self,
        stmt: &'mir MicroMirStatement<'tcx>,
        location: Location,
    ) -> EncodingResult<PCS<'tcx>> {
        if let Some(r) = stmt.precondition() {
            return Ok(r);
        }

        // State-dependent preconditions we can elaborate:
        //   - Kill of a MIR place
        //          INIT p => { e p }
        //          ALLOC p & !INIT p => { u p }
        match stmt {
            MicroMirStatement::Kill(None, LinearResource::Mir(p)) => {
                self.analysis_as_permission(p, location).map_or_else(
                    || {
                        Err(PrustiError::internal(
                            "could not find permission in analyses",
                            MultiSpan::new(),
                        ))
                    },
                    |perm| Ok(PCS::from_vec(vec![perm])),
                )
            }
            _ => Err(PrustiError::unsupported(
                "unsupported kill elaboration",
                MultiSpan::new(),
            )),
        }
    }

    // TODO: contains prefix of??
    // What about partial drops?
    fn analysis_as_permission(
        &self,
        p: &Place<'tcx>,
        location: Location,
    ) -> Option<PCSPermission<'tcx>> {
        if self
            .init_analysis
            .get_before_statement(location)
            .contains_prefix_of(*p)
        {
            return Some(PCSPermission::new_initialized(
                Mutability::Mut,
                LinearResource::Mir(*p),
            ));
        } else if self
            .alloc_analysis
            .get_before_statement(location)
            .contains_prefix_of(*p)
        {
            return Some(PCSPermission::new_initialized(
                Mutability::Mut,
                LinearResource::Mir(*p),
            ));
        } else {
            return None;
        }
    }

    fn elaborate_postcondition(
        &self,
        stmt: &'mir MicroMirStatement<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        stmt.postcondition().ok_or(PrustiError::unsupported(
            "postconditions can not be elaborated",
            MultiSpan::new(),
        ))
    }

    /// Computes the unification between two PCS's, inserts packs and repacks as necessary
    fn repack(
        &self,
        mut pcs: PCS<'tcx>,
        next_pre: &PCS<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        RepackUnify::unify_moves(&pcs, next_pre, self.mir, self.env)?.apply_packings(
            pcs,
            &mut op_mir.statements,
            &mut op_mir.pcs_before,
        )
    }

    fn packup(
        &self,
        mut pcs: PCS<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        RepackPackup::new(self.env.tcx(), self.mir, pcs.clone())?.apply_packings(
            pcs,
            &mut op_mir.statements,
            &mut op_mir.pcs_before,
        )
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
    // PCS A -- unpacks -- trim --.
    //                           join -- packs --> PCS C
    // PCS B -- unpacks -- trim --'
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
    mut pcs: PCS<'tcx>,
    pre: &PCS<'tcx>,
    post: &PCS<'tcx>,
) -> EncodingResult<PCS<'tcx>> {
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

    return Ok(pcs);
}
