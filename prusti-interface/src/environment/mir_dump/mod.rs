use super::Environment;
use crate::environment::mir_dump::graphviz::Graph;
use prusti_common::config;
use rustc_span::def_id::DefId;
use std::path::PathBuf;

mod graphviz;
mod lifetimes;
mod mir;

pub(crate) fn dump_mir_info(env: &Environment<'_>, def_id: DefId) {
    eprintln!("def_id: {:?}", def_id);
    let local_def_id = def_id.expect_local();
    let def_path = env.tcx().hir().def_path(local_def_id);

    if let Some(graph) = mir::populate_graph(env, def_id) {
        prusti_common::report::log::report_with_writer(
            "graphviz_mir_dump",
            format!("{}.dot", def_path.to_filename_friendly_no_crate()),
            |writer| graph.write(writer).unwrap(),
        );
    } else {
        eprintln!("Failed to populate the graph.");
    }
}
