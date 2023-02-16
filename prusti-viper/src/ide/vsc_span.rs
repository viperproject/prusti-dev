use prusti_rustc_interface::span::{source_map::SourceMap, Span};
use serde::{Serialize, Deserialize};
/// a representation of spans that is more usable with VSCode.
#[derive(Serialize, Clone)]
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

impl VscSpan {
    pub fn from_span(sp: &Span, sourcemap: &SourceMap) -> Option<Self> {
        let filename = sourcemap.span_to_filename(*sp);
        let diag_filename = sourcemap.filename_for_diagnostics(&filename);
        let fname = format!("{}", diag_filename);

        if let Ok((l1, l2)) = sourcemap.is_valid_span(*sp) {
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
