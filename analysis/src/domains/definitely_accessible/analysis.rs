// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::{DefinitelyAccessibleState, DefinitelyInitializedAnalysis, MaybeBorrowedAnalysis},
    PointwiseState,
};
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::def_id::DefId;

pub struct DefinitelyAccessibleAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> DefinitelyAccessibleAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        DefinitelyAccessibleAnalysis {
            tcx,
            def_id,
            body_with_facts,
        }
    }

    pub fn run_analysis(
        &self,
    ) -> AnalysisResult<PointwiseState<'mir, 'tcx, DefinitelyAccessibleState>> {
        let body = &self.body_with_facts.body;
        let def_init_analysis =
            DefinitelyInitializedAnalysis::new_relaxed(self.tcx, self.def_id, body);
        let def_init = def_init_analysis.run_fwd_analysis()?;
        let borrowed_analysis = MaybeBorrowedAnalysis::new(self.body_with_facts);
        let borrowed = borrowed_analysis.run_analysis()?;
        let mut analysis_state = PointwiseState::default(body);

        // Set state_after_block
        for (block, block_data) in body.basic_blocks().iter_enumerated() {
            for statement_index in 0..=block_data.statements.len() {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                let def_init_before = def_init
                    .lookup_before(location)
                    .unwrap_or_else(|| panic!("No 'def_init' state after location {:?}", location));
                let borrowed_before = borrowed
                    .lookup_before(location)
                    .unwrap_or_else(|| panic!("No 'borrowed' state after location {:?}", location));
                // TODO: analysis_state.set_before(location, ...);
            }
            let def_init_after_block = def_init
                .lookup_after_block(block)
                .unwrap_or_else(|| panic!("No 'def_init' state after block {:?}", block));
            let borrowed_after_block = borrowed
                .lookup_after_block(block)
                .unwrap_or_else(|| panic!("No 'borrowed' state after block {:?}", block));
            let available_after_block = analysis_state.lookup_mut_after_block(block);
            for &successor in block_data.terminator().successors() {
                let def_init_after = def_init_after_block.get(&successor).unwrap_or_else(|| {
                    panic!("No 'def_init' state from {:?} to {:?}", block, successor)
                });
                let borrowed_after = borrowed_after_block.get(&successor).unwrap_or_else(|| {
                    panic!("No 'borrowed' state from {:?} to {:?}", block, successor)
                });
                // TODO: available_after_block.set(successor, ...)
            }
        }

        Ok(analysis_state)
    }
}
