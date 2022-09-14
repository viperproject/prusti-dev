use super::Environment;
use crate::environment::{
    mir_body::{borrowck::facts::LocationTable, graphviz::to_graphviz},
    Procedure,
};
use prusti_rustc_interface::span::def_id::DefId;
use vir::common::graphviz::Graph;

pub(crate) fn dump_mir_info(env: &Environment<'_>, def_id: DefId) {
    eprintln!("def_id: {def_id:?}");
    let local_def_id = def_id.expect_local();
    let def_path = env.query.hir().def_path(local_def_id);

    if let Some(graph) = populate_graph(env, def_id) {
        prusti_common::report::log::report_with_writer(
            "graphviz_mir_dump",
            format!("{}.dot", def_path.to_filename_friendly_no_crate()),
            |writer| graph.write(writer).unwrap(),
        );
    } else {
        eprintln!("Failed to populate the graph.");
    }
}

fn populate_graph(env: &Environment<'_>, def_id: DefId) -> Option<Graph> {
    eprintln!("populate_graph: {def_id:?}");
    let procedure = Procedure::new(env, def_id);
    let mir = procedure.get_mir();
    if let Some(facts) = env
        .body
        .try_get_local_mir_borrowck_facts(def_id.expect_local())
    {
        let input_facts = facts.input_facts.borrow().as_ref().unwrap().clone();
        let location_table = LocationTable::new(facts.location_table.borrow().as_ref().unwrap());
        Some(to_graphviz(&input_facts, &location_table, mir, &Vec::new()))
    } else {
        None
    }
}
