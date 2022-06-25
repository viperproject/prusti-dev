// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::mir_utils::location_to_stmt_str;
use prusti_rustc_interface::middle::mir;

#[derive(Debug)]
pub enum AnalysisError {
    UnsupportedStatement(mir::Location),
    /// The state is not defined before the given location.
    NoStateBeforeLocation(mir::Location),
    /// The state is not defined after the given MIR block.
    NoStateAfterBlock(mir::BasicBlock),
    /// The state is not defined on the edge between two MIR blocks (source, destination).
    NoStateAfterSuccessor(mir::BasicBlock, mir::BasicBlock),
}

impl AnalysisError {
    pub fn to_pretty_str(&self, mir: &mir::Body) -> String {
        match self {
            AnalysisError::UnsupportedStatement(location) => {
                let stmt = location_to_stmt_str(*location, mir);
                format!("Unsupported statement at {:?}: {}", location, stmt)
            }
            AnalysisError::NoStateBeforeLocation(location) => {
                let stmt = location_to_stmt_str(*location, mir);
                format!(
                    "There is no state before the statement at {:?} ({})",
                    location, stmt
                )
            }
            AnalysisError::NoStateAfterBlock(bb) => {
                let terminator = &mir[*bb].terminator();
                format!(
                    "There is no state after the terminator of block {:?} ({:?})",
                    bb, terminator.kind
                )
            }
            AnalysisError::NoStateAfterSuccessor(bb_src, bb_dst) => {
                let terminator = &mir[*bb_src].terminator();
                format!(
                    "There is no state for the block {:?} after the terminator of block {:?} ({:?})",
                    bb_dst, bb_src, terminator.kind
                )
            }
        }
    }
}
