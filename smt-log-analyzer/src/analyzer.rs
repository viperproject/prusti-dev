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
    let trace_quantifier_triggers = std::env::var("PRUSTI_SMT_TRACE_QUANTIFIER_TRIGGERS")
        .ok()
        .map(|value| value.parse().unwrap());
    let settings = Settings {
        write_statistics: true,
        quantifier_instantiations_ignore_builtin: false,
        quantifier_instantiations_bound_global_kind: None,
        quantifier_instantiations_bound_trace: None,
        quantifier_instantiations_bound_trace_kind: None,
        unique_triggers_bound: None,
        unique_triggers_bound_total: None,
        check_active_scopes_count: Some(0),
        pop_scopes_by_one: false,
        trace_quantifier_triggers,
    };
    analyze(&PathBuf::from(input_file), settings)
}
