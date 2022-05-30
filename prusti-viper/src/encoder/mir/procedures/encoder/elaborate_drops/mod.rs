use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    Encoder,
};
use prusti_common::config;
use prusti_interface::environment::{
    mir_body::{
        borrowck::{
            facts::{validation::validate, LocationTable},
            lifetimes::Lifetimes,
        },
        graphviz::to_graphviz,
        patch::apply_patch,
    },
    Procedure,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir;

mod mir_dataflow;
pub(super) mod mir_transform;

pub(super) fn elaborate_drops<'v, 'tcx: 'v>(
    encoder: &mut Encoder<'v, 'tcx>,
    def_id: DefId,
    procedure: &Procedure<'tcx>,
) -> SpannedEncodingResult<(mir::Body<'tcx>, Lifetimes)> {
    let (mut input_facts, mut location_table) = if let Some(facts) = encoder
        .env()
        .try_get_local_mir_borrowck_facts(def_id.expect_local())
    {
        let input_facts = facts.input_facts.borrow().as_ref().unwrap().clone();
        let location_table = LocationTable::new(facts.location_table.borrow().as_ref().unwrap());
        (input_facts, location_table)
    } else {
        return Err(SpannedEncodingError::internal(
            format!("failed to obtain borrow information for {:?}", def_id),
            procedure.get_span(),
        ));
    };
    let mir = procedure.get_mir();
    let tcx = encoder.env().tcx();

    if config::dump_debug_info() {
        let local_def_id = def_id.expect_local();
        let def_path = encoder.env().tcx().hir().def_path(local_def_id);
        let graph = to_graphviz(&input_facts, &location_table, mir);
        prusti_common::report::log::report_with_writer(
            "graphviz_mir_dump_before_patch",
            format!("{}.dot", def_path.to_filename_friendly_no_crate()),
            |writer| graph.write(writer).unwrap(),
        );
    }

    validate(&input_facts, &location_table, mir);
    let drop_patch = self::mir_transform::run_pass(tcx, mir);
    let mir = apply_patch(drop_patch, mir, &mut input_facts, &mut location_table);

    if config::dump_debug_info() {
        let local_def_id = def_id.expect_local();
        let def_path = encoder.env().tcx().hir().def_path(local_def_id);
        let graph = to_graphviz(&input_facts, &location_table, &mir);
        prusti_common::report::log::report_with_writer(
            "graphviz_mir_dump_after_patch",
            format!("{}.dot", def_path.to_filename_friendly_no_crate()),
            |writer| graph.write(writer).unwrap(),
        );
    }

    validate(&input_facts, &location_table, &mir);

    let lifetimes = Lifetimes::new(input_facts, location_table);

    Ok((mir, lifetimes))
}
