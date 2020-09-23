// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]

extern crate rustc_middle;
extern crate rustc_span;

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;
use rustc_span::def_id::LocalDefId;

pub struct LivenessState {}
pub struct DefinitelyInitializedState {}
pub struct PCSState {}

pub trait AnalysisResult {
    type AbstractState;
    fn lookup(&self, location: mir::Location) -> Self::AbstractState;
}

pub enum AnalysisError {
    UnsupportedStatement(mir::Location),
}

type Result<T> = std::result::Result<T, AnalysisError>;

pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    // We can add caching, using e.g. a RefCell<HashMap<LocalDefId, Result<...>>>
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer {
            tcx,
        }
    }

    // Instead of `mir: &mir::Body<'tcx>` we could ask for a `LocalDefId`, which can be resolved
    // using https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.mir_promoted
    pub fn liveness_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = LivenessState>>> {
        unimplemented!();
    }

    pub fn definitely_initilized_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = DefinitelyInitializedState>>> {
        unimplemented!();
    }

    pub fn pcs_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = PCSState>>> {
        unimplemented!();
    }
}
