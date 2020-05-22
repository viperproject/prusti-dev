use rustc_ast::ast;
use rustc_resolve::Resolver;

/// Rewrite the crate so that the compiler checks the specifications for us.
pub(crate) fn rewrite_crate(_krate: &mut ast::Crate, _resolver: &mut Resolver) {}
