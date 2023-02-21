use super::{call_finder, query_signature};
use prusti_interface::{environment::Environment, specs::typed};
use prusti_rustc_interface::{
    hir::def_id::DefId,
    span::{source_map::SourceMap, Span},
};
use prusti_viper::ide::vsc_span::VscSpan;
use serde::{ser::SerializeStruct, Serialize};

// create some struct storing all the information the IDE will ever need.
// needs to be transformable into json!

#[derive(Serialize)]
pub struct IdeInfo {
    procedure_defs: Vec<ProcDef>,
    function_calls: Vec<ProcDef>,
    queried_source: Option<String>,
    // additionally this will contain:
    // function_calls:
    // ... we'll see
}

impl IdeInfo {
    pub fn collect(env: &Environment<'_>, procedures: &Vec<DefId>, def_spec: &typed::DefSpecificationMap) -> Self {
        let procs = collect_procedures(env, procedures, def_spec);
        let source_map = env.tcx().sess.source_map();
        let fncalls: Vec<ProcDef> = collect_fncalls(env)
            .into_iter()
            .map(|(name, defid, sp)| ProcDef {
                name,
                defid,
                span: VscSpan::from_span(&sp, source_map).unwrap(),
            })
            .collect();

        // For declaring external specifications:
        let queried_source = query_signature::collect_queried_signature(env.tcx(), &fncalls);
        Self {
            procedure_defs: procs,
            function_calls: fncalls,
            queried_source,
        }
    }
}

pub struct ProcDef {
    pub name: String,
    pub defid: DefId,
    pub span: VscSpan,
}

// defid is not needed for VSCode and not serializable as of now..
impl Serialize for ProcDef {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("ProcDef", 2)?;
        state.serialize_field("name", &self.name)?;
        state.serialize_field("span", &self.span)?;
        state.end()
    }
}


// collect information about the program that will be passed to IDE:
fn collect_procedures(env: &Environment<'_>, procedures: &Vec<DefId>, def_spec: &typed::DefSpecificationMap) -> Vec<ProcDef> {
    let sourcemap: &SourceMap = env.tcx().sess.source_map();
    let mut procs = Vec::new();
    for defid in procedures {
        let defpath = env.name.get_unique_item_name(*defid);
        let span = env.query.get_def_span(defid);
        let vscspan = VscSpan::from_span(&span, sourcemap).unwrap();
        
        // Filter out the predicates and trusted methods,
        // since we don't want to allow selective verification
        // for them
        let mut is_predicate = false;
        let mut is_trusted = false;

        let proc_spec_opt = def_spec.get_proc_spec(defid);
        if let Some(proc_spec) = proc_spec_opt {
            let kind_spec = proc_spec.base_spec.kind.extract_with_selective_replacement();
            let trusted_spec = proc_spec.base_spec.trusted.extract_with_selective_replacement();
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

fn collect_fncalls(env: &Environment<'_>) -> Vec<(String, DefId, Span)> {
    // let l_hir = env.tcx().hir();
    // let hir_body = l_hir.body();

    let mut fnvisitor = call_finder::CallSpanFinder::new(env);

    // let mut adjusted_visitor =
    // fnvisitor.visit_body(hir_body);
    env.tcx()
        .hir()
        .visit_all_item_likes_in_crate(&mut fnvisitor);

    return fnvisitor.called_functions;
}

