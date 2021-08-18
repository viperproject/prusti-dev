use std::io::Write;

use rustc_data_structures::sync::Lrc;
use rustc_errors::{emitter::Emitter, registry::Registry, Handler, HandlerFlags};
use rustc_session::{config, parse::ParseSess, DiagnosticOutput};
use rustc_span::source_map::SourceMap;

mod export_error_emitter;

pub use export_error_emitter::ExportErrorEmitter;

pub fn replace_emitter(
    sopts: config::Options,
    registry: rustc_errors::registry::Registry,
    dest: Option<Box<dyn Write + std::marker::Send>>,
) -> Box<dyn FnOnce(&mut ParseSess) + std::marker::Send> {
    box |sess: &mut ParseSess| {
        let flags = sopts.debugging_opts.diagnostic_handler_flags(true);
        sess.span_diagnostic =
            build_handler_with_emitter(sopts, registry, dest, sess.clone_source_map(), flags);
    }
}

fn build_handler_with_emitter(
    sopts: config::Options,
    registry: rustc_errors::registry::Registry,
    dest: Option<Box<dyn Write + std::marker::Send>>,
    source_map: Lrc<SourceMap>,
    flags: HandlerFlags,
) -> Handler {
    Handler::with_emitter_and_flags(
        box ExportErrorEmitter::new(sopts, registry, source_map, dest),
        flags,
    )
}
