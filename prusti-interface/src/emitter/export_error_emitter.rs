use rustc_data_structures::sync::{self, Lrc};
use rustc_errors::{
    annotate_snippet_emitter_writer::AnnotateSnippetEmitterWriter,
    emitter::{ColorConfig, Destination, Emitter, EmitterWriter, HumanReadableErrorType},
    json::JsonEmitter,
    registry::Registry,
    Diagnostic, DiagnosticId, Handler,
};
/// A set of structs and fns to access the info compiler use to construct a session
use rustc_session::config;
/// A struct for mapping source code and files
use rustc_span::source_map::SourceMap;
use std::io::Write;

pub struct ExportErrorEmitter {
    inner: Box<dyn Emitter>,
}

impl Emitter for ExportErrorEmitter {
    fn emit_diagnostic(&mut self, diag: &Diagnostic) {
        self.custom_emit(diag);
    }
    fn source_map(&self) -> Option<&Lrc<SourceMap>> {
        self.inner.as_ref().source_map()
    }
}

impl ExportErrorEmitter {
    pub fn new(
        sopts: config::Options,
        registry: rustc_errors::registry::Registry,
        source_map: Lrc<SourceMap>,
        emitter_dest: Option<Box<dyn Write + std::marker::Send>>,
    ) -> Self {
        Self {
            inner: build_inner_emitter(&sopts, registry, source_map, emitter_dest),
        }
    }

    fn custom_emit(&mut self, diag: &Diagnostic) {
        if let Some(DiagnosticId::Error(err_code)) = &diag.code {
            if err_code == "E0428"
                && diag
                    .message
                    .iter()
                    .any(|(err_msg, _)| err_msg.contains("prusti_export_"))
            {
                let mut diag = diag.to_owned();
                for (msg, _) in diag.message.iter_mut() {
                    self.rewrite_error_msg(msg);
                }
                self.inner.as_mut().emit_diagnostic(&diag);
            } else {
                self.inner.as_mut().emit_diagnostic(diag);
            }
        } else {
            self.inner.as_mut().emit_diagnostic(diag);
        }
    }

    /// The fn rewrite the msg stored in diagnostic
    /// Currently we only target the error msg that is redefinition of prusti-export macro
    /// Example: "multiple define of prusti_export_ident_hash" -> "duplicate specification for ident"
    fn rewrite_error_msg(&self, msg: &mut String) {
        let msg_vec: Vec<&str> = msg.split('_').collect();
        let len = msg_vec.len();
        if len >= 4 {
            *msg = format!(
                "[Prusti: invalid specification] duplicate export specification for {}",
                msg_vec[2..(len - 1)].join("")
            );
        }
    }
}

/// This function is built on rustc src to create default emitter
/// https://github.com/rust-lang/rust/blob/3d0774d0dc98084d25d95cc1909a8051ebbd9cb1/compiler/rustc_session/src/session.rs#L1129-L1191
fn build_inner_emitter(
    sopts: &config::Options,
    registry: rustc_errors::registry::Registry,
    source_map: Lrc<SourceMap>,
    emitter_dest: Option<Box<dyn Write + std::marker::Send>>,
) -> Box<dyn Emitter + sync::Send> {
    let macro_backtrace = sopts.debugging_opts.macro_backtrace;
    match (sopts.error_format, emitter_dest) {
        (config::ErrorOutputType::HumanReadable(kind), dst) => {
            let (short, color_config) = kind.unzip();

            if let HumanReadableErrorType::AnnotateSnippet(_) = kind {
                let emitter =
                    AnnotateSnippetEmitterWriter::new(Some(source_map), short, macro_backtrace);
                Box::new(emitter.ui_testing(sopts.debugging_opts.ui_testing))
            } else {
                let emitter = match dst {
                    None => EmitterWriter::stderr(
                        color_config,
                        Some(source_map),
                        short,
                        sopts.debugging_opts.teach,
                        sopts.debugging_opts.terminal_width,
                        macro_backtrace,
                    ),
                    Some(dst) => EmitterWriter::new(
                        dst,
                        Some(source_map),
                        short,
                        false, // no teach messages when writing to a buffer
                        false, // no colors when writing to a buffer
                        None,  // no terminal width
                        macro_backtrace,
                    ),
                };
                Box::new(emitter.ui_testing(sopts.debugging_opts.ui_testing))
            }
        }
        (
            config::ErrorOutputType::Json {
                pretty,
                json_rendered,
            },
            None,
        ) => Box::new(
            JsonEmitter::stderr(
                Some(registry),
                source_map,
                pretty,
                json_rendered,
                sopts.debugging_opts.terminal_width,
                macro_backtrace,
            )
            .ui_testing(sopts.debugging_opts.ui_testing),
        ),
        (
            config::ErrorOutputType::Json {
                pretty,
                json_rendered,
            },
            Some(dst),
        ) => Box::new(
            JsonEmitter::new(
                dst,
                Some(registry),
                source_map,
                pretty,
                json_rendered,
                sopts.debugging_opts.terminal_width,
                macro_backtrace,
            )
            .ui_testing(sopts.debugging_opts.ui_testing),
        ),
    }
}
