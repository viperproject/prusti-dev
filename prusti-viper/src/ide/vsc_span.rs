use prusti_rustc_interface::span::{source_map::SourceMap, Span};
use serde::Serialize;

/// a representation of spans that is more usable with VSCode.
#[derive(Serialize, Clone)]
pub struct VscSpan {
    column_end: usize,
    column_start: usize,
    line_end: usize,
    line_start: usize,
    file_name: String,
    is_primary: bool,
}

impl VscSpan {
    pub fn from_span(sp: &Span, sourcemap: &SourceMap) -> Self {
        let span_filename = sourcemap.span_to_filename(*sp);
        let diag_filename = sourcemap.filename_for_diagnostics(&span_filename);
        let file_name = format!("{diag_filename}");

        let (l1, l2) = sourcemap.is_valid_span(*sp).expect("Invalid span");
        Self {
            column_start: l1.col.0,
            column_end: l2.col.0,
            line_start: l1.line,
            line_end: l2.line,
            file_name,
            // the following one is not relevant here, we just want to be
            // able to reuse the existing methods and the parser
            // for spans in VSCode
            is_primary: false,
        }
    }
}
