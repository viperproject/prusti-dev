// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;

#[derive(Debug)]
pub enum AnalysisError {
    UnsupportedStatement(mir::Location),
    SuccessorWithoutState(mir::Location, mir::BasicBlock),      // Location of Terminator & successor BB without state
}
