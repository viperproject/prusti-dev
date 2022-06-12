#![deny(unused_must_use)]

//! The Z3 log format is documented
//! [here](https://github.com/viperproject/axiom-profiler/blob/master/LogDocumentation.pdf).

use error::Error;
use parser::{EventKind, Parser, QuantTerm};
use state::State;
use std::{
    fs::File,
    io::{BufRead, BufReader},
};

mod error;
mod parser;
mod state;
mod types;

#[derive(Default)]
struct Settings {
    pop_by_one: bool,
}

fn process_line(settings: &Settings, state: &mut State, line: &str) -> Result<(), Error> {
    let mut parser = Parser::from_line(line);
    match parser.parse_event_kind()? {
        EventKind::Pop => {
            let scopes_to_pop = parser.parse_number()?;
            let active_scopes_count = parser.parse_number()?;
            parser.check_eof()?;
            assert_eq!(state.active_scopes_count(), active_scopes_count);
            if settings.pop_by_one {
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
        EventKind::MkQuant => {
            if let Ok(id) = parser.parse_id() {
                // We are ignoring the builtin quantifiers that have non-numeric
                // ids such as datatype#6
                let name = parser.parse_name()?;
                state.register_quantifier(id, name);
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
            }
        }
        EventKind::Unrecognized => {}
    }
    Ok(())
}

fn main() -> Result<(), std::io::Error> {
    // TODO: Collect the quantifier definitions from the smt file.
    let mut args = std::env::args();
    assert!(args.next().is_some());
    let input_file = args.next().expect("Z3 log file expected");
    assert!(args.next().is_none(), "Only one argument was expected");
    let file = File::open(&input_file)?;
    let mut reader = BufReader::new(file);

    let settings = Settings { pop_by_one: true };
    let mut state = State::default();

    let mut line = String::new();
    let mut line_number = 0;
    while reader.read_line(&mut line)? > 0 {
        line_number += 1;
        process_line(&settings, &mut state, &line)
            .unwrap_or_else(|error| panic!("Error {} on line {}", error, line_number));
        line.clear();
    }
    state.write_statistics(&input_file);
    assert_eq!(state.active_scopes_count(), 0);
    Ok(())
}
