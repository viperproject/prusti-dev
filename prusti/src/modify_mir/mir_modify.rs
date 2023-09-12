use crate::modify_mir::{mir_helper::*, mir_info_collector::MirInfo, passes};
use prusti_interface::utils;
use prusti_rustc_interface::{
    hir::def::DefKind,
    index::IndexVec,
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

/// Insert checks into the MIR
pub(crate) fn insert_runtime_checks<'tcx>(
    body: &mut mir::Body<'tcx>,
    def_id: DefId,
    tcx: TyCtxt<'tcx>,
    local_decls: &IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
) {
    if matches!(tcx.def_kind(def_id), DefKind::AnonConst) {
        return;
    }

    let mir_info = MirInfo::collect_mir_info(tcx, body.clone(), def_id);
    // MAKE MODIFICATIONS:
    let mut old_arg_replacer = passes::CloneOldArgs::new(tcx, &mir_info, def_id, local_decls);
    // first we just create locals for old clones and replace them where arguments
    // should be evaluated in an old state. We need to do this early, because we rely
    // on positions of assignments to variables to be accurate. We can not insert the
    // cloning here too, because that would also offset locations for other passes
    // that follow
    old_arg_replacer.create_and_replace_variables(body);

    // insert pledge checks:
    passes::PledgeInserter::run(tcx, &mir_info, def_id, local_decls, body);

    // insert a dummy goto block at the beginning of the body, so we can easily
    // insert blocks at the beginning of the function
    prepend_dummy_block(body);
    // insert preconditions
    passes::PreconditionInserter::run(tcx, &mir_info, def_id, local_decls, body);
    // insert postconditions
    passes::PostconditionInserter::run(tcx, &mir_info, def_id, local_decls, body);
    // replace predicates with their check functions:
    passes::PredicateReplacer::run(tcx, &mir_info, def_id, body);

    // insert cloning of arguments if they are used within old, and drop them again
    old_arg_replacer.clone_and_drop_variables(body);

    // store specs and env back into globals
    mir_info.store_specs_env();
}

/// Perform optimizations based on the verification results
pub fn dead_code_elimination<'tcx>(tcx: TyCtxt<'tcx>, body: &mut mir::Body<'tcx>, def_id: DefId) {
    // no modifications to spec functions!
    let attrs = tcx.get_attrs_unchecked(def_id);
    if utils::has_spec_only_attr(attrs) {
        return;
    }
    passes::DeadCodeElimination::run(tcx, def_id, body);
}
