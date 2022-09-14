#![deny(unused_must_use)]
#![warn(clippy::disallowed_types)]

//! The Z3 log format is documented
//! [here](https://github.com/viperproject/axiom-profiler/blob/master/LogDocumentation.pdf).

use error::Error;
use parser::{EventKind, Parser, QuantTerm};
use state::State;
use std::{
    fs::File,
    io::{BufRead, BufReader},
};
use types::{QuantifierId, BUILTIN_QUANTIFIER_ID};

mod error;
mod parser;
mod state;
mod types;

pub struct Settings {
    pub write_statistics: bool,
    pub quantifier_instantiations_ignore_builtin: bool,
    pub quantifier_instantiations_bound_global_kind: Option<u64>,
    pub quantifier_instantiations_bound_trace: Option<u64>,
    pub quantifier_instantiations_bound_trace_kind: Option<u64>,
    pub unique_triggers_bound: Option<u64>,
    pub unique_triggers_bound_total: Option<u64>,
    pub check_active_scopes_count: Option<u32>,
    pub pop_scopes_by_one: bool,
    /// If Some, dumps all triggers that match the specified quantifier.
    pub trace_quantifier_triggers: Option<QuantifierId>,
}

fn process_line(settings: &Settings, state: &mut State, line: &str) -> Result<(), Error> {
    let mut parser = Parser::from_line(line);
    let event_kind = parser.parse_event_kind()?;
    state.register_event_kind(event_kind);
    match event_kind {
        EventKind::Pop => {
            let scopes_to_pop = parser.parse_number()?;
            let active_scopes_count = parser.parse_number()?;
            parser.check_eof()?;
            assert_eq!(state.active_scopes_count(), active_scopes_count);
            if settings.pop_scopes_by_one {
                let mut scopes_to_pop = scopes_to_pop;
                while scopes_to_pop > 0 {
                    state.pop_scopes(1);
                    scopes_to_pop -= 1;
                }
            } else {
                state.pop_scopes(scopes_to_pop);
            }
        }
        EventKind::Push => {
            let active_scopes_count = parser.parse_number()?;
            parser.check_eof()?;
            assert_eq!(state.active_scopes_count(), active_scopes_count);
            state.push_scope();
        }
        EventKind::MkApp => {
            if let Some(term_id) = parser.try_parse_id()? {
                let ident = parser.parse_name()?;
                if ident.starts_with("basic_block_marker") {
                    state.register_label(ident.to_string());
                } else {
                    let name = ident.to_string();
                    let mut args = Vec::new();
                    while let Some(arg) = parser.try_parse_id()? {
                        args.push(arg);
                    }
                    state.register_term_function_application(term_id, name, args);
                }
            }
        }
        EventKind::MkVar => {
            if let Some(term_id) = parser.try_parse_id()? {
                let index = parser.parse_number()?;
                state.register_term_bound_variable(term_id, index);
            }
        }
        EventKind::AttachMeaning => {
            let term_id = parser.parse_id()?;
            let ident = parser.parse_name()?;
            let ident = ident.to_string();
            parser.skip_whitespace();
            let remaining = parser.remaining();
            state.register_term_attach_meaning(term_id, ident, remaining);
        }
        EventKind::MkQuant => {
            if let Ok(id) = parser.parse_id() {
                // We are ignoring the builtin quantifiers that have non-numeric
                // ids such as datatype#6
                let name = parser.parse_name()?;
                state.register_quantifier(id, name.to_string());
            }
        }
        EventKind::NewMatch => {
            let fingerprint = parser.parse_hex_number()?;
            if fingerprint != 0 {
                // Built-in quantifiers have fingerprint 0; ignore them.
                let quantifier_id = parser.parse_id()?;
                state.register_matched_quantifier(quantifier_id)?;
                let _trigger_id = parser.parse_id()?;
                while let Some(_variable_instantiation) = parser.try_parse_id()? {}
                parser.consume(';')?;
                while let Some(matched_term) = parser.try_parse_quant_term()? {
                    match matched_term {
                        QuantTerm::Single(matched) => {
                            state.register_matched_trigger_term(quantifier_id, matched)?;
                        }
                        QuantTerm::Pair(original, matched) => {
                            state.register_matched_trigger_term(quantifier_id, original)?;
                            state.register_matched_trigger_term(quantifier_id, matched)?;
                        }
                    }
                }
                parser.check_eof()?;
            } else {
                state.register_matched_quantifier(BUILTIN_QUANTIFIER_ID)?;
            }
        }
        EventKind::InstDiscovered => {
            let name = parser.parse_name()?;
            assert_eq!(name, "theory-solving");
            let fingerprint = parser.parse_hex_number()?;
            assert_eq!(fingerprint, 0);
            let theory = parser.parse_theory()?;
            state.register_inst_discovered(theory)?;
        }
        EventKind::Instance => {
            state.register_instance()?;
        }
        EventKind::DecideAndOr => {
            let term_id = parser.parse_id()?;
            let undef_child_id = parser.parse_id()?;
            // FIXME: This information seems to be useless.
            state.register_decide_and_or_term(term_id, undef_child_id);
        }
        _ => {}
    }
    Ok(())
}

pub fn analyze(
    z3_trace_path: &std::path::PathBuf,
    settings: Settings,
) -> Result<(), std::io::Error> {
    // TODO: Collect the quantifier definitions from the smt file.

    let file = File::open(z3_trace_path)?;
    let mut reader = BufReader::new(file);

    let mut state = State::default();

    // Builtin quantifiers have fingerprint 0.
    state.register_quantifier(BUILTIN_QUANTIFIER_ID, "builtin quantifier".to_string());

    // Theories.
    state.register_theory(parser::TheoryKind::Arith);
    state.register_theory(parser::TheoryKind::Basic);
    state.register_theory(parser::TheoryKind::Datatype);
    state.register_theory(parser::TheoryKind::UserSort);

    // Tracing triggers.
    state.mark_quantifier_for_tracing(settings.trace_quantifier_triggers);

    let mut line = String::new();
    let mut prev_line = String::new();
    let mut line_number = 0;
    assert!(reader.read_line(&mut prev_line)? > 0);
    while reader.read_line(&mut line)? > 0 {
        // We use this `prev_line` to avoid processing the last line, which is
        // very likely to be invalid because Silicon kills Z3.
        std::mem::swap(&mut line, &mut prev_line);
        line_number += 1;
        process_line(&settings, &mut state, &line)
            .unwrap_or_else(|error| panic!("Error {error} on line {line_number}"));
        line.clear();
    }
    let scopes_left = state.active_scopes_count();
    state.pop_all_scopes();
    let input_file = z3_trace_path.to_str().unwrap();
    if settings.write_statistics {
        state.write_statistics(input_file);
    }
    if let Some(expected_scopes_count) = settings.check_active_scopes_count {
        assert_eq!(scopes_left, expected_scopes_count);
    }
    state.check_bounds(
        input_file,
        settings.quantifier_instantiations_ignore_builtin,
        settings.quantifier_instantiations_bound_global_kind,
        settings.quantifier_instantiations_bound_trace,
        settings.quantifier_instantiations_bound_trace_kind,
        settings.unique_triggers_bound,
        settings.unique_triggers_bound_total,
    );
    Ok(())
}
