// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that invokes the verifier `prusti-viper`

use specifications::TypedSpecificationMap;
use prusti_viper::verifier::VerifierBuilder as ViperVerifierBuilder;
use prusti_interface::verifier::VerifierBuilder;
use prusti_interface::verifier::VerificationContext;
use prusti_interface::verifier::Verifier;
use prusti_interface::data::VerificationTask;
use prusti_interface::data::VerificationResult;
use rustc_driver::driver;
use rustc::hir::intravisit;
use syntax::{self, ast, parse, ptr, attr};
use syntax::codemap::Span;
use environment::Environment;
use environment::Procedure;
use hir_visitor::HirVisitor;
use rustc::hir;
use rustc::mir::{Mir, Mutability, Operand, Projection, ProjectionElem, Rvalue};
use rustc_mir::borrow_check::{MirBorrowckCtxt, do_mir_borrowck};
use rustc_mir::borrow_check::flows::Flows;
use rustc_mir::borrow_check::prefixes::*;
use rustc_mir::dataflow::FlowsAtLocation;
use rustc::mir::{BasicBlock, BasicBlockData, VisibilityScope, ARGUMENT_VISIBILITY_SCOPE};
use rustc::mir::Location;
use rustc::mir::Place;
use rustc::mir::BorrowKind;
use rustc_mir::dataflow::move_paths::HasMoveData;
use rustc_mir::dataflow::move_paths::MovePath;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::indexed_vec::Idx;
use std::fs::File;
use std::io::{Write, BufWriter};
use rustc_mir::dataflow::move_paths::MoveOut;
use std::collections::{HashSet, HashMap};
use rustc_mir::dataflow::BorrowData;
use rustc::ty::{Region, RegionKind, FreeRegion, BoundRegion, RegionVid, TypeVariants};
use std::fmt;
use rustc_mir::borrow_check::nll::ToRegionVid;
use std::hash::{Hash, Hasher, SipHasher};
use rustc_mir::borrow_check::nll::region_infer::{RegionDefinition, Constraint};
use std::collections::hash_map::DefaultHasher;
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::ty::{self, Ty, TyCtxt};


/// Verify a (typed) specification on compiler state.
pub fn verify<'r, 'a: 'r, 'tcx: 'a>(
    state: &'r mut driver::CompileState<'a, 'tcx>,
    spec: TypedSpecificationMap,
) {
    trace!("[verify] enter");

    debug!("Specification consists of {} elements.", spec.len());

    let env = Environment::new(state);

    debug!("Dump borrow checker info...");
    env.dump_borrowck_info();

    debug!("Prepare verification task...");
    let annotated_procedures = env.get_annotated_procedures();
    let verification_task = VerificationTask { procedures: annotated_procedures };

    debug!("Prepare verifier...");
    let verifier_builder = ViperVerifierBuilder::new();
    let verification_context = VerifierBuilder::<Procedure>::new_verification_context(&verifier_builder);
    let mut verifier = verification_context.new_verifier(&env);

    debug!("Run verifier...");
    let verification_result = verifier.verify(&verification_task);
    debug!("Verifier returned {:?}", verification_result);

    match verification_result {
        VerificationResult::Success => info!("Prusti verification succeded"),
        VerificationResult::Failure => env.err("Prusti verification failed"),
    };

    trace!("[verify] exit");
}
