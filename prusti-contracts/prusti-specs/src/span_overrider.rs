use proc_macro2::Span;

/// Override all span information
pub struct SpanOverrider {
    span: Span,
}

impl SpanOverrider {
    pub fn new(span: Span) -> Self {
        SpanOverrider { span }
    }
}

impl syn::visit_mut::VisitMut for SpanOverrider {
    fn visit_span_mut(&mut self, span: &mut Span) {
        *span = self.span;
    }
}
