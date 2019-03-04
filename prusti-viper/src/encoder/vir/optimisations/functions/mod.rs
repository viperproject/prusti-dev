//! A module that contains optimisations for functions.

mod inliner;

pub use self::inliner::inline_constant_functions;
