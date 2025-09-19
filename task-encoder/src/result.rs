use prusti_rustc_interface::span::Span;

use super::*;

/// The result of an `encode` call.
pub type EncodeResult<'vir, E /*: TaskEncoder + 'vir + ?Sized*/> = Result<
    Option<(
        <E as TaskEncoder>::OutputRef<'vir>,
        <E as TaskEncoder>::OutputFullLocal<'vir>,
        <E as TaskEncoder>::OutputFullDependency<'vir>,
    )>,
    TaskEncoderError<E>,
>;

/// The result of the actual encoder implementation (`do_encode_full`).
pub type EncodeFullResult<'vir, E /*: TaskEncoder + 'vir + ?Sized*/> = Result<
    (
        <E as TaskEncoder>::OutputFullLocal<'vir>,
        <E as TaskEncoder>::OutputFullDependency<'vir>,
    ),
    EncodeFullError<'vir, E>,
>;

/// An unsuccessful result occurring in `do_encode_full`.
pub enum EncodeFullError<'vir, E: TaskEncoder + 'vir + ?Sized> {
    /// Indicates that the current task has already been encoded. This can
    /// occur when there are cyclic dependencies between multiple encoders.
    /// This error is specifically returned when one encoder depends on
    /// another encoder (using e.g. `TaskEncoderDependencies::require_ref`),
    /// that latter encoder then depending on the former again, causing the
    /// former encoder to complete its full encoding in the inner invocation.
    /// The outer invocation remains on the stack, but will be aborted early
    /// as soon as the control flow returns to it.
    AlreadyEncoded,

    /// An actual error occurred during encoding.
    EncodingError(
        <E as TaskEncoder>::EncodingError,
        Option<E::OutputFullDependency<'vir>>,
    ),

    DependencyError(Vec<(&'static str, String, Vec<Span>)>),
}

// Manual implementation, since neither `E` nor `E::OutputFullDependency` are
// required to be `Debug`.
impl<'vir, E: TaskEncoder + 'vir + ?Sized> std::fmt::Debug for EncodeFullError<'vir, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyEncoded => write!(f, "AlreadyEncoded"),
            Self::EncodingError(err, _output_dep) => f
                .debug_tuple("EncodingError")
                .field(err) /*.field(output_dep)*/
                .finish(),
            Self::DependencyError(..) => write!(f, "DependencyError"),
        }
    }
}

pub enum TaskEncoderError<E: TaskEncoder + ?Sized> {
    EnqueueingError(<E as TaskEncoder>::EnqueueingError),
    EncodingError(<E as TaskEncoder>::EncodingError),
    DependencyError(Vec<(&'static str, String, Vec<Span>)>),
    CyclicError,
}

impl<E: TaskEncoder + ?Sized> std::fmt::Debug for TaskEncoderError<E>
where
    <E as TaskEncoder>::EncodingError: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EncodingError(err) => f.debug_tuple("EncodingError").field(err).finish(),
            Self::EnqueueingError(err) => f.debug_tuple("EnqueueingError").field(err).finish(),
            Self::DependencyError(err) => f.debug_tuple("DependencyError").field(err).finish(),
            Self::CyclicError => write!(f, "CyclicError"),
        }
    }
}

// manual implementation because derive adds Clone on all generic parameters
impl<E: TaskEncoder + ?Sized> Clone for TaskEncoderError<E> {
    fn clone(&self) -> Self {
        match self {
            Self::EncodingError(err) => Self::EncodingError(err.clone()),
            Self::EnqueueingError(err) => Self::EnqueueingError(err.clone()),
            Self::DependencyError(stack) => Self::DependencyError(stack.clone()),
            Self::CyclicError => Self::CyclicError,
        }
    }
}
