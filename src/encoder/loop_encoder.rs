// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::mir;
use prusti_interface::environment::ProcedureLoops;

pub struct LoopEncoder {
    pub loop_info: ProcedureLoops,
}

impl LoopEncoder {

    pub fn new<'a, 'tcx: 'a>(mir: &'a mir::Mir<'tcx>) -> LoopEncoder {
        LoopEncoder {
            loop_info: ProcedureLoops::new(mir),
        }
    }

}
