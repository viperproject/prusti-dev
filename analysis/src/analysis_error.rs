// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::serialization_utils::location_to_stmt_str;
use rustc_middle::mir;

#[derive(Debug)]
pub enum AnalysisError {
    UnsupportedStatement(mir::Location),
    /// *Contains the Location of Terminator & successor BB without state*
    SuccessorWithoutState(mir::Location, mir::BasicBlock),
}

impl AnalysisError {
    pub fn to_pretty_str(&self, mir: &mir::Body) -> String {
        match self {
            AnalysisError::UnsupportedStatement(location) => {
                let stmt = location_to_stmt_str(*location, mir);
                format!("Unsupported statement at {:?}: {}", location, stmt)
            }
            AnalysisError::SuccessorWithoutState(location, bb) => {
                let stmt = location_to_stmt_str(*location, mir);
                format!(
                    "Basic block {:?} after terminator at {:?} ({}) has no state assigned",
                    bb, location, stmt
                )
            }
        }
    }
}
