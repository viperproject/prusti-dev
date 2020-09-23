// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_ast;
extern crate rustc_attr;

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;

pub struct LivenessAnalysisState {}
pub struct DefinitelyInitializedAnalysisState {}
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
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer {
            tcx,
        }
    }

    pub fn liveness_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = LivenessAnalysisState>>> {
        unimplemented!();
    }

    pub fn definitely_initilized_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = DefinitelyInitializedAnalysisState>>> {
        unimplemented!();
    }

    pub fn pcs_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<Box<dyn AnalysisResult<AbstractState = PCSState>>> {
        unimplemented!();
    }
}