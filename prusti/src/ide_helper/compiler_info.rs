use super::{call_finder, query_signature};
use prusti_interface::{environment::Environment, specs::typed};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    span::{source_map::SourceMap, Span},
};
use prusti_viper::ide::vsc_span::VscSpan;
use serde::Serialize;

/// This struct will be passed to prusti-assistant containing information
/// about the program that is currently being verified
#[derive(Serialize)]
pub struct IdeInfo {
    procedure_defs: Vec<ProcDef>,
    function_calls: Vec<ProcDef>,
    queried_source: Option<String>,
}

impl IdeInfo {
    pub fn collect(
        env: &Environment<'_>,
        procedures: &Vec<DefId>,
        def_spec: &typed::DefSpecificationMap,
    ) -> Self {
        let procedure_defs = collect_procedures(env, procedures, def_spec);
        let source_map = env.tcx().sess.source_map();
        let function_calls = collect_fncalls(env)
            .into_iter()
            .map(|(name, defid, sp)| ProcDef {
                name,
                defid,
                span: VscSpan::from_span(&sp, source_map),
            })
            .collect::<Vec<_>>();

        // For declaring external specifications:
        let queried_source = query_signature::collect_queried_signature(env.tcx(), &function_calls);
        Self {
            procedure_defs,
            function_calls,
            queried_source,
        }
    }
}

/// A struct that contains either a reference to a procedure that can be verified
/// (for selective verification) or a function call (so a user can query
/// external_spec blocks for it). The name contains the defpath.
#[derive(Serialize)]
pub struct ProcDef {
    pub name: String,
    #[serde(skip)]
    pub defid: DefId,
    pub span: VscSpan,
}

/// collect information about the program that will be passed to IDE.
/// This should find all non-trusted functions that can be verified
fn collect_procedures(
    env: &Environment<'_>,
    procedures: &Vec<DefId>,
    def_spec: &typed::DefSpecificationMap,
) -> Vec<ProcDef> {
    let sourcemap: &SourceMap = env.tcx().sess.source_map();
    let mut procs = Vec::new();
    for defid in procedures {
        let defpath = env.name.get_unique_item_name(*defid);
        let span = env.query.get_def_span(defid);
        let vscspan = VscSpan::from_span(&span, sourcemap);

        // Filter out the predicates and trusted methods,
        // since we don't want to allow selective verification
        // for them
        let mut is_predicate = false;
        let mut is_trusted = false;

        let proc_spec_opt = def_spec.get_proc_spec(defid);
        if let Some(proc_spec) = proc_spec_opt {
            let kind_spec = proc_spec
                .base_spec
                .kind
                .extract_with_selective_replacement();
            let trusted_spec = proc_spec
                .base_spec
                .trusted
                .extract_with_selective_replacement();
            if let Some(typed::ProcedureSpecificationKind::Predicate(..)) = kind_spec {
                is_predicate = true;
            }
            if let Some(true) = trusted_spec {
                is_trusted = true;
            }
        }

        if !is_trusted && !is_predicate {
            procs.push(ProcDef {
                name: defpath,
                defid: *defid,
                span: vscspan,
            });
        }
    }
    procs
}

/// collect all the function calls, so the extension can query external_spec
/// templates for it
fn collect_fncalls(env: &Environment<'_>) -> Vec<(String, DefId, Span)> {
    let mut fnvisitor = call_finder::CallSpanFinder::new(env);
    env.tcx()
        .hir()
        .visit_all_item_likes_in_crate(&mut fnvisitor);

    fnvisitor.called_functions
}
