#![deny(unused_must_use)]

//! The Z3 log format is documented
//! [here](https://github.com/viperproject/axiom-profiler/blob/master/LogDocumentation.pdf).

use smt_log_analyzer::{analyze, Settings};
use std::path::PathBuf;

fn main() -> Result<(), std::io::Error> {
    let mut args = std::env::args();
    assert!(args.next().is_some());
    let input_file = args.next().expect("Z3 log file expected");
    assert!(args.next().is_none(), "Only one argument was expected");
    let settings = Settings {
        write_statistics: true,
        quantifier_instantiations_ignore_builtin: false,
        quantifier_instantiations_bound_global_kind: None,
        quantifier_instantiations_bound_trace: None,
        quantifier_instantiations_bound_trace_kind: None,
        check_active_scopes_count: Some(0),
        pop_scopes_by_one: false,
    };
    analyze(&PathBuf::from(input_file), settings)
}
