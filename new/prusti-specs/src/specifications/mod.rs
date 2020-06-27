/// Each atomic Prusti assertion (`A`) is a Rust expression (`E`)
/// or a `forall` expression. Atomic Prusti assertions can be joined together
/// using the following two operators, forming Prusti assertions:
/// - `A && A` (conjunction)
/// - `A ==> A` (implication)
///
/// `==>` has weaker binding than `&&` and is right-associative.
///
/// Parentheses can be used as usual, i.e. `(A ==> A) && A`
/// is a Prusti assertion.
///
/// `forall` expression has the following syntax
/// (`A` is an arbitrary Prusti assertion):
/// `forall(|NAME1: TYPE1, NAME2: TYPE2, ...| A)`
/// `forall(|NAME1: TYPE1, NAME2: TYPE2, ...| A, triggers=[(E, ...), ...])`
///
/// Prusti assertions can only be joined together by `&&` and `==>`, for example
/// the following is not allowed, since `(E ==> E)` is a Prusti assertion:
/// `(E ==> E) || E`
///
/// However, this is fine, as `&&` is also a Rust operator, and this whole thing
/// is interpreted as a Rust expression:
/// `(E && E) || E`
///
/// Having `&&` and `||` in the same subexpression is not allowed to prevent
/// ambiguities. Those are all illegal:
/// `E && E || E`
/// `A && (E && E || E)`
///
/// However, this is fine, since the implication resolves the ambiguity:
/// (note that both the lhs and rhs of the implication form a Prusti assertion)
/// `E && E ==> E || E`
///
/// Basic parser usage (`tokens` is of type `proc_macro2::TokenStream`):
/// ```rust
/// let mut parser = Parser::from_token_stream(tokens);
/// let assertion = parser.extract_assertion()?;
/// ```

pub mod common;
pub mod json;
pub mod untyped;
pub mod preparser;

pub use common::SpecType;
