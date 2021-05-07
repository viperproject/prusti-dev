//! An interface to the compiler.
// Most code here are copied from the Rust compiler sources. See its license for
// details.

use rustc_hir::{def_id::DefId};
use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_middle::ty::RegionVid;
use rustc_infer::infer::{InferCtxt, TyCtxtInferExt};
use rustc_mir::borrow_check::universal_regions::UniversalRegions;
use rustc_mir::borrow_check::renumber::renumber_mir;
use rustc_index::vec::IndexVec;
use std::rc::Rc;
use rustc_mir::borrow_check::type_check::free_region_relations::CreateResult;
use rustc_mir::borrow_check::member_constraints::MemberConstraintSet;
use rustc_mir::borrow_check::type_check::MirTypeckRegionConstraints;
use rustc_mir::borrow_check::constraints::OutlivesConstraintSet;
use rustc_mir::borrow_check::region_infer::values::LivenessValues;
use rustc_mir::borrow_check::region_infer::values::PlaceholderIndices;
use rustc_mir::borrow_check::type_check::free_region_relations;
use rustc_mir::borrow_check::region_infer::values::RegionValueElements;
use rustc_mir::borrow_check::location::LocationTable;
use rustc_mir::borrow_check::borrow_set::BorrowSet;
use rustc_mir::dataflow::MoveDataParamEnv;
use rustc_mir::dataflow::move_paths::MoveData;
use rustc_middle::mir::Place;
use rustc_mir::dataflow::move_paths::MoveError;
use rustc_mir::borrow_check::facts::AllFacts;

/// Enrich the given `mir::Body` with the lifetime information.
pub(in crate::environment::borrowck2) fn enrich_mir_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    input_body: &mir::Body<'tcx>
) -> super::MirBody<'tcx> {
    let mut result = None;
    let result_borrow = &mut result;
    tcx.infer_ctxt().enter(|infcx| {
        *result_borrow = Some(collect_borrowck_info(&infcx, input_body));
    });
    let (universal_regions, universal_regions_outlives, body, all_facts_opt, location_table) = result.unwrap();
    let polonius_facts = all_facts_opt.unwrap();
    let local_names = super::derive::extract_local_names(&body);
    super::MirBody {
        def_id,
        body,
        tcx,
        universal_regions,
        universal_regions_outlives,
        polonius_facts,
        location_table,
        local_names
    }
}

fn collect_borrowck_info<'tcx>(
    infcx: &InferCtxt<'_, 'tcx>,
    input_body: &mir::Body<'tcx>,
) -> (Vec<RegionVid>, Vec<(RegionVid, RegionVid)>, mir::Body<'tcx>, Option<AllFacts>, LocationTable) {
    let tcx = infcx.tcx;

    let mut body = input_body.clone();

    // Renumber the lifetimes in MIR.
    let def = input_body.source.with_opt_param().as_local().unwrap();
    let param_env = tcx.param_env(def.did);
    let universal_regions = Rc::new(
        UniversalRegions::new(infcx, def, param_env));
    let mut promoted = IndexVec::new(); // TODO: How to get promoted for MIR optimized?
    renumber_mir(infcx, &mut body, &mut promoted);

    // Obtain the lifetime constraints between universal lifetimes.
    let elements = &Rc::new(RegionValueElements::new(&body));
    let mut constraints = MirTypeckRegionConstraints {
        placeholder_indices: PlaceholderIndices::default(),
        placeholder_index_to_region: IndexVec::default(),
        liveness_constraints: LivenessValues::new(elements.clone()),
        outlives_constraints: OutlivesConstraintSet::default(),
        member_constraints: MemberConstraintSet::default(),
        closure_bounds_mapping: Default::default(),
        type_tests: Vec::default(),
    };

    let implicit_region_bound = infcx.tcx.mk_region(ty::ReVar(universal_regions.fr_fn_body));

    let CreateResult {
        universal_region_relations,
        region_bound_pairs,
        normalized_inputs_and_output,
    } = free_region_relations::create(
        infcx,
        param_env,
        Some(implicit_region_bound),
        &universal_regions,
        &mut constraints,
    );

    let mut all_facts = Some(Default::default());
    let location_table = LocationTable::new(&body);
    let (move_data, _move_errors): (MoveData<'tcx>, Vec<(Place<'tcx>, MoveError<'tcx>)>) =
    match MoveData::gather_moves(&body, tcx, param_env) {
        Ok(move_data) => (move_data, Vec::new()),
        Err((move_data, move_errors)) => (move_data, move_errors),
    };
    let mdpe = MoveDataParamEnv { move_data, param_env };
    let id = tcx.hir().local_def_id_to_hir_id(def.did);
    let locals_are_invalidated_at_exit = tcx.hir().body_owner_kind(id).is_fn_or_closure();
    let borrow_set = BorrowSet::build(tcx, &body, locals_are_invalidated_at_exit, &mdpe.move_data);

    use rustc_mir::borrow_check::constraint_generation;
    constraint_generation::generate_constraints(
        infcx,
        &mut constraints.liveness_constraints,
        &mut all_facts,
        &location_table,
        &body,
        &borrow_set,
    );

    let fn_universal_regions = universal_regions.universal_regions().collect::<Vec<_>>();
    let universal_region_outlives = universal_region_relations.known_outlives().map(|(r1, r2)| (*r1, *r2)).collect::<Vec<_>>();

    (fn_universal_regions, universal_region_outlives, body, all_facts, location_table)
}