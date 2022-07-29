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

            for (next_block, dependent_postcondition) in terminator.postcondition() {
                //      Apply the semantics (we are now joinable mod repacks)
                let mut this_pcs = transform_pcs(
                    pcs.clone(),
                    &terminator.precondition(),
                    &dependent_postcondition,
                )?;

                // Trim the PCS by way of eager drops (we are now the same mod repacks)
                this_pcs = self.trim_pcs(this_pcs);

                // Pack to the most packed state possible (we are now identical)
                // (any unique state works)
                let mut this_op_mir = StraightOperationalMir::default();
                this_pcs = self.packup(this_pcs, &mut this_op_mir)?;

                // If the next block is not added, add it as a dirty block
                todo!();

                // Otherwise, just perform a runtime check that the PCS's before
                //  the first statement are the same

                todo!();
            }
        }
        todo!();
    }

    // Straight-line PCS computation inside the body of a basic block
    fn translate_body(
        &self,
        block_data: &MicroMirData<'tcx>,
        op_mir: &mut StraightOperationalMir<'tcx>,
        mut pcs: PCS<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        for statement in block_data.statements.iter() {
            // 1. Elaborate the state-dependent conditions
            let statement_precondition = self.elaborate_precondition(statement)?;
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
    fn trim_pcs(&self, mut pcs: PCS<'tcx>) -> PCS<'tcx> {
        todo!();
    }

    /// Elaborate the precondition of a statement
    fn elaborate_precondition(
        &self,
        stmt: &'mir MicroMirStatement<'tcx>,
    ) -> EncodingResult<PCS<'tcx>> {
        // 1. collect the precondition from it's hoare semantics
        // 2. if the precondition is None
        //     2.1. if the statement is a kill of a (MIR) place p
        //              INIT p  => return { e p }
        //              ALLOC p => return { u p }
        //              neither => error!
        //     2.2. (no other statements have undetermined preconditions in this model)
        //              return precondition

        stmt.precondition().ok_or(
            // State-dependent preconditions we can elaborate:
            //   - Kill of a MIR place
            //          INIT p => { e p }
            //          ALLOC p & !INIT p => { u p }
            match stmt {
                // MicroMirStatement::Kill(None, LinearResource::Mir(p)) => {
                //     match
                // }
                _ => todo!(),
            },
        )
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
