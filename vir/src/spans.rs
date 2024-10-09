use std::collections::HashMap;
use prusti_interface::PrustiError;
use prusti_rustc_interface::span::Span;
use crate::VirCtxt;

pub struct VirSpanHandler<'vir> {
    error_kind: &'static str,
    handler: Box<dyn Fn(Option<Span>) -> Option<Vec<PrustiError>> + 'vir>,
    next: Option<Box<VirSpanHandler<'vir>>>,
}

#[derive(Hash)]
pub struct VirSpan<'vir> {
    pub id: usize,
    span: Span,
    parent: Option<&'vir VirSpan<'vir>>,
}

unsafe impl<'vir> Send for VirSpan<'vir> {}
unsafe impl<'vir> Sync for VirSpan<'vir> {}

impl serde::Serialize for VirSpan<'_> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where S: serde::ser::Serializer
    {
        ser.serialize_u64(self.id as u64)
    }
}
impl<'de> serde::Deserialize<'de> for VirSpan<'_> {
    fn deserialize<D>(deser: D) -> Result<Self, D::Error>
    where D: serde::de::Deserializer<'de>
    {
        let id = u64::deserialize(deser)? as usize;
        Ok(VirSpan {
            id,
            span: Default::default(),
            parent: None,
        })
    }
}

/// The span manager. Maintains a vector of all allocated spans, as well as
/// the stack, used when allocating AST nodes.
#[derive(Default)]
pub struct VirSpanManager<'vir> {
    /// Vector of all allocated spans. The `id` field of a `VirSpan` is an
    /// index into this vector. The same `id` can thus be used as the position
    /// ID given to Viper over JNI, and when backtranslating error positions
    /// can be used to index into this vector again, to find any error
    /// transformers.
    all: Vec<&'vir crate::spans::VirSpan<'vir>>,

    /// Stack of "current" spans. This is maintained such that an encoder can
    /// walk down the MIR primitives recursively, adding their stacks onto the
    /// stack as it works. At the same time, these spans will be linked with
    /// their parent, i.e. the preceding span in the stack. This parent link
    /// can be used during error backtranslation to find the closest ancestor
    /// to an offending node with an error transformer.
    // TODO: it might be good to insert sentinel nodes into the stack whenever
    //   crossing an encoder context (e.g. when a different encoder is used as
    //   part of a `deps.require_*` call) to avoid linking unrelated spans
    //   together
    stack: Vec<&'vir crate::spans::VirSpan<'vir>>,

    handlers: HashMap<usize, VirSpanHandler<'vir>>,
}

impl<'tcx> VirCtxt<'tcx> {
    /// Execute the given function with the given span (temporarily) added to
    /// the span stack.
    pub fn with_span<T>(&'tcx self, span: Span, f: impl FnOnce(&'tcx Self) -> T) -> T {
        let mut manager = self.spans.borrow_mut();
        let span = self.alloc(VirSpan {
            id: manager.all.len(),
            span,
            parent: manager.stack.last().copied(),
        });
        manager.all.push(span);
        manager.stack.push(span);
        let len_before = manager.stack.len();
        drop(manager);
        let res = f(self);
        let mut manager = self.spans.borrow_mut();
        debug_assert_eq!(manager.stack.len(), len_before);
        manager.stack.pop().unwrap();
        res
    }

    /// Add an error handler to the span currently on top of the stack.
    /// `error_kind` is the machine-readable identifier of an error, as
    /// defined by Viper. The handler function should construct one or more
    /// `PrustiError`s to report the error with the correct span etc.
    pub fn handle_error(
        &'tcx self,
        error_kind: &'static str,
        handler: impl Fn(Option<Span>) -> Option<Vec<PrustiError>> + 'tcx,
    ) {
        let top_span_id = self.top_span().unwrap().id;
        let mut manager = self.spans.borrow_mut();
        let previous = manager.handlers.remove(&top_span_id);
        manager.handlers.insert(top_span_id, VirSpanHandler {
            error_kind,
            handler: Box::new(handler),
            next: previous.map(Box::new),
        });
    }

    // TODO: eventually, this should not be an Option
    pub fn top_span(&'tcx self) -> Option<&'tcx VirSpan<'tcx>> {
        self.spans.borrow().stack.last().copied()
    }

    /// Attempt to backtranslate the given error at the given position.
    pub fn backtranslate(
        &'tcx self,
        error_kind: &str,
        offending_pos_id: usize,
        reason_pos_id: Option<usize>,
     ) -> Option<Vec<PrustiError>> {
        let manager = self.spans.borrow();
        let reason_span_opt = reason_pos_id
            .and_then(|id| manager.all.get(id))
            .map(|vir_span| vir_span.span);
        let mut span_opt = manager.all.get(offending_pos_id);
        while let Some(span) = span_opt {
            let mut handler_opt = manager.handlers.get(&span.id);
            while let Some(handler) = handler_opt {
                if handler.error_kind == error_kind {
                    if let Some(errors) = (handler.handler)(reason_span_opt) {
                        return Some(errors);
                    }
                }
                handler_opt = handler.next.as_deref();
            }
            span_opt = span.parent.as_ref();
        }
        None
    }
}
