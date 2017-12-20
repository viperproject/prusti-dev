/// A collection of spans. Spans have two orthogonal attributes:
///
/// - they can be *primary spans*. In this case they are the locus of
///   the error, and would be rendered with `^^^`.
/// - they can have a *label*. In this case, the label is written next
///   to the mark in the snippet when we render.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct MultiSpan {
    primary_spans: Vec<Span>,
    span_labels: Vec<(Span, String)>,
}

/// A compressed span.
/// Contains either fields of `SpanData` inline if they are small, or index into span interner.
/// The primary goal of `Span` is to be as small as possible and fit into other structures
/// (that's why it uses `packed` as well). Decoding speed is the second priority.
/// See `SpanData` for the info on span fields in decoded representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(packed)]
pub struct Span(u32);
