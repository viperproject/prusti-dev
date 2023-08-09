use crate::modify_mir::{mir_helper::*, mir_info_collector::MirInfo, passes};
use prusti_interface::utils;
use prusti_rustc_interface::{
    index::IndexVec,
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub(crate) fn insert_runtime_checks<'tcx>(
    body: &mut mir::Body<'tcx>,
    def_id: DefId,
    tcx: TyCtxt<'tcx>,
    local_decls: &IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
) {
    let mir_info = MirInfo::collect_mir_info(tcx, body.clone(), def_id, &local_decls);

    // MAKE MODIFICATIONS:
    // replace old arguments
    let mut old_arg_replacer = passes::CloneOldArgs::new(tcx, &mir_info, def_id, &local_decls);
    // first we just create locals for old clones and replace them where arguments
    // should be evaluated in an old state
    old_arg_replacer.create_variables(body);

    // insert pledge checks:
    let mut pledge_inserter = passes::PledgeInserter::new(tcx, &mir_info, def_id, &local_decls);
    pledge_inserter.run(body);
    // insert a dummy goto block at the beginning of the body
    prepend_dummy_block(body);
    // insert preconditions
    let mut precondition_inserter =
        passes::PreconditionInserter::new(tcx, &mir_info, def_id, &local_decls);
    precondition_inserter.run(body);
    // insert postconditions
    let mut postcondition_inserter =
        passes::PostconditionInserter::new(tcx, &mir_info, def_id, &local_decls);
    postcondition_inserter.run(body);
    old_arg_replacer.clone_and_drop_variables(body);

    // put specs and env back into globals
    mir_info.store_specs_env();
}

pub fn insert_asserts_for_reachability<'tcx>(
    body: &mut mir::Body<'tcx>,
    def_id: DefId,
    tcx: TyCtxt<'tcx>,
) {
    // this might be over the line, but for now, for every block we insert
    // an assert!(false)
    let attrs = tcx.get_attrs_unchecked(def_id);
    if utils::has_spec_only_attr(attrs) {
        return;
    }
    let local_decls = body.local_decls.clone();
    let mut assertion_inserter = passes::AssertionInserter::new(tcx, def_id, &local_decls);
    assertion_inserter.run(body);
}

pub fn dead_code_elimination<'tcx>(tcx: TyCtxt<'tcx>, body: &mut mir::Body<'tcx>, def_id: DefId) {
    // no modifications to spec functions!
    let attrs = tcx.get_attrs_unchecked(def_id);
    if utils::has_spec_only_attr(attrs) {
        return;
    }
    let local_decls = body.local_decls.clone();
    let mut insert_remove_assertions = passes::AssertionInserter::new(tcx, def_id, &local_decls);
    insert_remove_assertions.undo_insertions(body);
    let mut remove_dead_blocks = passes::DeadCodeElimination::new(tcx, def_id);
    remove_dead_blocks.run(body);
}
