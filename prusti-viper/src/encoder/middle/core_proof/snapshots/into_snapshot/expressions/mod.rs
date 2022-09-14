/// Expressions that are framed and used in pure contexts. For example, pure
/// function bodies.
mod pure_framed;
/// Expressions to be used in procedure bodies. For example, arguments of
/// builtin methods.
mod procedure_bodies;

pub(in super::super::super) use self::{
    procedure_bodies::PlaceToSnapshot, pure_framed::FramedExpressionToSnapshot,
};
