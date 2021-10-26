// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;

/// Convert a `location` to a string representing the statement or terminator at that `location`
pub fn location_to_stmt_str(location: mir::Location, mir: &mir::Body) -> String {
    let bb_mir = &mir[location.block];
    if location.statement_index < bb_mir.statements.len() {
        let stmt = &bb_mir.statements[location.statement_index];
        format!("{:?}", stmt)
    } else {
        // location = terminator
        let terminator = bb_mir.terminator();
        format!("{:?}", terminator.kind)
    }
}
