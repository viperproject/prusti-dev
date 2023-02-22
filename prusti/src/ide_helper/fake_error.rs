use prusti_interface::environment::Environment;
use prusti_rustc_interface::{errors::MultiSpan, span::DUMMY_SP};

pub fn fake_error(env: Environment) {
    let sp = MultiSpan::from_span(DUMMY_SP);
    let message = String::from("[Prusti: FakeError]");
    let help = None;
    let notes = [];

    env.diagnostic
        .span_err_with_help_and_notes(sp, &message, &help, &notes);
}
