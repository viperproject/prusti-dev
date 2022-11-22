use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;

use prusti_rustc_interface::span::{
        Span,
        source_map::SourceMap,
    };

use serde::Serialize;
use super::call_finder;

// create some struct storing all the information the IDE will ever need.
// needs to be transformable into json!

#[derive(Serialize)]
pub struct IdeInfo {
    procedure_defs: Vec<ProcDef>,
    function_calls: Vec<ProcDef>,
    // additionally this will contain:
    // function_calls:
    // ... we'll see
}

#[derive(Serialize)]
pub struct ProcDef {
    name: String,
    span: VscSpan,
}

/// a representation of spans that is more usable with VSCode.
#[derive(Serialize)]
pub struct VscSpan {
    column_end: usize,
    column_start: usize,
    line_end: usize,
    line_start: usize,
    file_name: String,
    is_primary: bool,
    label: Option<()>,
    expansion: Option<()>,
}

// collect information about the program that will be passed to IDE:
pub fn collect_procedures(env: &Environment<'_>, verification_task: &VerificationTask) -> Vec<ProcDef>{
    let sourcemap: &SourceMap = env.tcx().sess.source_map();
    let mut procs = Vec::new();
    for procedure in &verification_task.procedures {
        let defpath = env.name.get_item_def_path(*procedure);
        let span = env.query.get_def_span(procedure);
        println!("found procedure: {}, span: {:?}", defpath, span);
        let vscspan = VscSpan::from_span(span, sourcemap).unwrap();

        procs.push(ProcDef{
            name: defpath, 
            span: vscspan
        });
    }
    procs
}

pub fn collect_fncalls(env: &Environment<'_>) -> Vec<(String, Span)>{
    // let l_hir = env.tcx().hir();
    // let hir_body = l_hir.body();

    let mut fnvisitor = call_finder::CallSpanFinder::new(env);
    // fnvisitor.visit_body(hir_body);
    env.tcx().hir().visit_all_item_likes_in_crate(&mut fnvisitor);

    return fnvisitor.spans;
}

impl IdeInfo {
    pub fn collect(env: &Environment<'_>, verification_task: &VerificationTask) -> Self {
        let procs = collect_procedures(env, verification_task);
        let source_map = env.tcx().sess.source_map();
        let fncalls = collect_fncalls(env).into_iter()
            .map(|(name, sp)| 
                ProcDef {
                    name, 
                    span: VscSpan::from_span(sp, source_map).unwrap()
                }
            )
            .collect();
        Self {
            procedure_defs: procs,
            function_calls: fncalls,
        }
    }
}




impl VscSpan {
    pub fn from_span(sp: Span, sourcemap: &SourceMap) -> Option<Self> {
        let filename = sourcemap.span_to_filename(sp);
        let diag_filename = sourcemap.filename_for_diagnostics(&filename);
        let fname = format!("{}", diag_filename);

        if let Ok((l1, l2)) = sourcemap.is_valid_span(sp) {
            Some(Self {
                column_end: l2.col.0,
                column_start: l1.col.0,
                line_end: l2.line,
                line_start: l2.line,
                file_name: fname,
                // the following 3 are not relevant here, we just want to be 
                // able to reuse the existing methods and the parser
                // for spans in VSCode
                is_primary: false,
                label: None,
                expansion: None,
            })
        } else {
            None
        }
    }
}
