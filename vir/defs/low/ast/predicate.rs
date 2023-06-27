use super::{expression::Expression, variable::VariableDecl};
use crate::common::display;

#[derive(Copy)]
pub enum PredicateKind {
    MemoryBlock,
    Owned,
    LifetimeToken,
    CloseFracRef,
    // /// Can be aliased, permission from range (0; 1)
    // WithoutSnapshotFrac,
    /// Can be aliased, permission is either 0 or 1.
    WithoutSnapshotWhole,
    /// Cannot be aliased, permission is either 0 or 1.
    WithoutSnapshotWholeNonAliased,
    /// Can be aliased, duplicable.
    DeadLifetimeToken,
    /// Cannot be aliased, identified by non-SSA lifetime.
    EndBorrowViewShift,
}

#[display(
    fmt = "predicate<{}> {}({}){}\n",
    kind,
    "name",
    "display::cjoin(parameters)",
    "display::option!(body, \" {{\n  {}\n}}\", \";\")"
)]
pub struct PredicateDecl {
    pub name: String,
    pub kind: PredicateKind,
    pub parameters: Vec<VariableDecl>,
    pub body: Option<Expression>,
}
