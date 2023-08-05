use crate::modify_mir::{mir_helper::*, mir_info_collector::MirInfo, passes};
use prusti_common::config;
use prusti_rustc_interface::{
    data_structures::steal::Steal,
    interface::DEFAULT_QUERY_PROVIDERS,
    middle::{mir, ty::TyCtxt},
    span::def_id::LocalDefId,
};

pub(crate) fn mir_drops_elaborated(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> &Steal<mir::Body<'_>> {
    if !config::insert_runtime_checks() {
        return (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, local_def_id);
    }
    // must be called before the drops_elaborated base query,
    // otherwise it will be stolen
    let (mir_promoted_steal, _) = tcx.mir_promoted(local_def_id);
    let mir_promoted_body = mir_promoted_steal.borrow().clone();
    let local_decls = mir_promoted_body.local_decls;

    let steal = (DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, local_def_id);
    let mut body = steal.steal();
    let def_id = local_def_id.to_def_id();

    let mir_info = MirInfo::collect_mir_info(tcx, body.clone(), def_id, &local_decls);

    // MAKE MODIFICATIONS:
    // replace old arguments
    let mut old_arg_replacer = passes::CloneOldArgs::new(tcx, &mir_info, def_id, &local_decls);
    // first we just create locals for old clones and replace them where arguments
    // should be evaluated in an old state
    old_arg_replacer.create_variables(&mut body);

    // insert pledge checks:
    let mut pledge_inserter = passes::PledgeInserter::new(tcx, &mir_info, def_id, &local_decls);
    pledge_inserter.run(&mut body);
    // insert a dummy goto block at the beginning of the body
    prepend_dummy_block(&mut body);
    // insert preconditions
    let mut precondition_inserter =
        passes::PreconditionInserter::new(tcx, &mir_info, def_id, &local_decls);
    precondition_inserter.run(&mut body);
    // insert postconditions
    let mut postcondition_inserter =
        passes::PostconditionInserter::new(tcx, &mir_info, def_id, &local_decls);
    postcondition_inserter.run(&mut body);
    old_arg_replacer.clone_and_drop_variables(&mut body);

    mir_info.store_specs_env();

    tcx.alloc_steal_mir(body)
}
