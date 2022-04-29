//! Methods for encoding SSA snapshot variables.

mod interface;
mod state;

pub(in super::super) use self::interface::SnapshotVariablesInterface;
pub(super) use self::state::{AllVariablesMap, VariableVersionMap};
