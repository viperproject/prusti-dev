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
use prusti_interface::{
    environment::{Environment, Procedure},
    utils::is_prefix,
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::stable_set::FxHashSet,
    errors::MultiSpan,
    middle::mir::{Body, Location, Mutability, Place},
};

pub mod straight;
use straight::*;

// Methods for computing the operational PCS
// Pass in the method with the DUMP_OPERATIONAL_PCS enviornment variable
//     straight        straight line, move-only PCS
//     conditional     conditionals and loops, move-only

/// Trait for any interpretation of the CFG.
///     Example: Move-only code can be a vector, loopless code
///         can be a DAG, etc.
pub trait CFG<CFGLocation, CFGStatement> {
    /// Location to start execution
    fn start(&self) -> CFGLocation;

    /// Location(s) of next places in control flow, possibly empty
    fn next(&self, l: CFGLocation) -> Vec<CFGLocation>;

    // MIR location, possibly many CFGLocations correspond to the same
    //  MIR source, certainly some do not (eg. pack/unpack)
    fn parent(&self, l: CFGLocation) -> Option<Location>;

    // MicroMir statement or terminator corresponding to the given location
    fn statement(&self, l: CFGLocation) -> EncodingResult<CFGStatement>;
}

/// Enviornments in which we compute the PCS
pub trait PCSEnv<'mir, 'env: 'mir, 'tcx: 'env> {
    /// Common data pieces for each analysis, carried around.
    fn get_env(&self) -> &'env Environment<'tcx>;
    fn get_mir(&self) -> &'mir Body<'tcx>;

    /// Every PCSEnv should have exactly one associated control flow scheme
    /// this scheme is populated according to the analysis
    type CFGLocation;
    type CFGStatement;
    type CF: CFG<Self::CFGLocation, Self::CFGStatement>;
    fn cfg(&mut self) -> &mut Self::CF;

    /// The goal of every PCSEnv is to populate the following function
    fn pcs_before(&self, l: Self::CFGLocation) -> EncodingResult<PCS<'tcx>>;
}
