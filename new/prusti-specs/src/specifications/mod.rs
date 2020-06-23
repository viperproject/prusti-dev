/// The parsing of Prusti assertions consists of the following steps:
/// - Split the input into atomic Prusti assertions (using operators `&&` and `==>` and `forall` keyword).
/// - Parse each atomic Prusti assertion using the parser for Rust expressions.
/// - From the parsed atomic assertions, assemble a composite one and return it as the result.

pub mod common;
pub mod json;
pub mod untyped;
pub mod preparser;

pub use common::SpecType;
