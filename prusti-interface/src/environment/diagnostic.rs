use prusti_rustc_interface::{
    errors::{Diag, EmissionGuarantee, MultiSpan},
    middle::ty::TyCtxt,
};
use std::cell::RefCell;

pub struct EnvDiagnostic<'tcx> {
    tcx: TyCtxt<'tcx>,
    warn_buffer: RefCell<Vec<prusti_rustc_interface::errors::Diag<'tcx, ()>>>,
}

impl<'tcx> EnvDiagnostic<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        EnvDiagnostic {
            tcx,
            warn_buffer: RefCell::new(Vec::new()),
        }
    }

    fn configure_diagnostic<S: Into<MultiSpan> + Clone, T: EmissionGuarantee>(
        diagnostic: &mut Diag<'tcx,T>,
        sp: S,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        diagnostic.span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg.clone());
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg.clone());
            } else {
                diagnostic.note(note_msg.clone());
            }
        }
    }

    /// Emits an error message.
    pub fn span_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.dcx().struct_err(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        for warn in self.warn_buffer.borrow_mut().drain(..) {
            warn.emit();
        }
        diagnostic.emit();
    }

    /// Emits a warning message.
    pub fn span_warn_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.dcx().struct_warn(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        diagnostic.emit();
    }

    /// Buffers a warning message, to be emitted on error.
    pub fn span_warn_on_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.dcx().struct_warn(msg.to_string());
        Self::configure_diagnostic(&mut diagnostic, sp, help, notes);
        self.warn_buffer.borrow_mut().push(diagnostic);
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.dcx().has_errors().is_some()
    }
}
