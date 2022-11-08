use std::{fmt, ptr::null};

use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;

use prusti_rustc_interface::{
    span::{
        Span, Loc,
        source_map::SourceMap,
        FileLines, FileLinesResult,
    },
};

use serde::Serialize;

// create some struct storing all the information the IDE will ever need.
// needs to be transformable into json!

#[derive(Serialize)]
pub struct IdeInfo {
    procedure_defs: Vec<(String, VscSpan)>,
    // additionally this will contain:
    // function_calls:
    // ... we'll see
}




impl IdeInfo {
    
    // collect information about the program that will be passed to IDE:
    pub fn collect_procedures(env: &Environment<'_>, verification_task: &VerificationTask) -> Self {
        let sourcemap: &SourceMap = env.tcx().sess.source_map();
        let mut procs = Vec::new();
        for procedure in &verification_task.procedures {
            let defpath = env.name.get_item_def_path(*procedure);
            let span = env.query.get_def_span(procedure);
            println!("found procedure: {}, span: {:?}", defpath, span);
            let vscspan = VscSpan::from_span(span, sourcemap).unwrap();
            procs.push((defpath, vscspan));
        }
        Self {
            procedure_defs: procs
        }

    }
}



/// a representation of spans that is more usable with VSCode.
#[derive(Serialize)]
pub struct VscSpan {
    from: (usize, usize),
    to: (usize, usize),
    filename: String,
}

impl VscSpan {
    pub fn from_span(sp: Span, sourcemap: &SourceMap) -> Option<Self> {
        let filename = sourcemap.span_to_filename(sp);
        let diag_filename = sourcemap.filename_for_diagnostics(&filename);
        let fname = format!("{}", diag_filename);

        if let Ok((l1, l2)) = sourcemap.is_valid_span(sp) {
            let loc1: Loc = l1;
            let loc2: Loc = l2;
            
            let line1 = loc1.line;
            let line2 = loc2.line;

            let char1 = loc1.col.0;
            let char2 = loc2.col.0;

            Some(Self {
                from: (line1, char1),
                to: (line2, char2),
                filename: fname,
            })
        } else {
        // println!("{:?}", lines);
        // match lines {
        //     Ok(fl) => {
        //
        //     },
        //     Err(_) => 
        // }
        // let parent = format!("{:?}", sp.parent().unwrap());
            None
        }
    }
}
