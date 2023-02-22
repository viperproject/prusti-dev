use prusti_interface::environment::Environment;
use prusti_rustc_interface::{errors::MultiSpan, span::DUMMY_SP};

/// This error will be thrown when skipping verification (which is done
/// when we just collect information for prusti-assistant), because then
/// a successful result will be cached and subsequent actual verifications succeed
/// (see issue #1261)
pub fn fake_error(env: Environment) {
    let sp = MultiSpan::from_span(DUMMY_SP);
    let message = String::from("[Prusti: FakeError]");
    let help = None;
    let notes = [];

    env.diagnostic
        .span_err_with_help_and_notes(sp, &message, &help, &notes);
}
