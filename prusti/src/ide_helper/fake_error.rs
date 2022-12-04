use prusti_interface::{
    environment::Environment,
    errors::{DiagnosticBuilder, EmissionGuarantee, MultiSpan},
};
use prusti_rustc_interface::span::span_encoding::DUMMY_SP;


pub fn fake_error(env: Environment<'tcx>) {
    let sp = MultiSpan::from_span(DUMMY_SP);
    let message = String::from("Not actually an error");
    let help = None;
    let notes = [];
    
    env.diagnostic.span_err_with_help_and_notes(sp, msg, &help, &notes);
}
