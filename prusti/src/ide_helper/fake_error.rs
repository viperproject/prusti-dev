use prusti_interface::environment::Environment;
use prusti_rustc_interface::{
    span::DUMMY_SP,
    errors::MultiSpan,
};


pub fn fake_error<'tcx>(env: Environment<'tcx>) {
    let sp = MultiSpan::from_span(DUMMY_SP);
    let message = String::from("[Prusti: FakeError]");
    let help = None;
    let notes = [];
    
    env.diagnostic.span_err_with_help_and_notes(sp, &message, &help, &notes);
}
