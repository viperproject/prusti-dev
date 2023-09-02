use crate::modify_mir::{mir_helper::*, mir_info_collector::MirInfo, passes};
use prusti_interface::utils;
use prusti_rustc_interface::{
    hir::def::DefKind,
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
    let mir_info = MirInfo::collect_mir_info(tcx, body.clone(), def_id, local_decls);
    let attrs = tcx.get_attrs_unchecked(def_id);
    let is_spec_fn = utils::has_spec_only_attr(attrs);
    let def_kind = tcx.def_kind(def_id);
    let is_anon_const = matches!(def_kind, DefKind::AnonConst);

    // MAKE MODIFICATIONS:
    // replace old arguments
    let mut old_arg_replacer = passes::CloneOldArgs::new(tcx, &mir_info, def_id, local_decls);
    // first we just create locals for old clones and replace them where arguments
    // should be evaluated in an old state
    old_arg_replacer.create_variables(body);

    // we dont insert pledge checks for specification functions
    if !is_spec_fn && !is_anon_const {
        // insert pledge checks:
        let mut pledge_inserter = passes::PledgeInserter::new(tcx, &mir_info, def_id, local_decls);
        pledge_inserter.run(body);
    }

    // insert a dummy goto block at the beginning of the body
    prepend_dummy_block(body);
    // insert preconditions
    let mut precondition_inserter =
        passes::PreconditionInserter::new(tcx, &mir_info, def_id, local_decls);
    precondition_inserter.run(body);
    // insert postconditions
    let mut postcondition_inserter =
        passes::PostconditionInserter::new(tcx, &mir_info, def_id, local_decls);
    postcondition_inserter.run(body);
    old_arg_replacer.clone_and_drop_variables(body);

    // put specs and env back into globals
    mir_info.store_specs_env();
}

pub fn dead_code_elimination<'tcx>(tcx: TyCtxt<'tcx>, body: &mut mir::Body<'tcx>, def_id: DefId) {
    // no modifications to spec functions!
    let attrs = tcx.get_attrs_unchecked(def_id);
    if utils::has_spec_only_attr(attrs) {
        return;
    }
    let mut remove_dead_blocks = passes::DeadCodeElimination::new(tcx, def_id);
    remove_dead_blocks.run(body);
}
