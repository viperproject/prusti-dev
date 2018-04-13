// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;
use rustc::mir;
use prusti_interface::environment::{BasicBlockIndex, PlaceAccess, ProcedureLoops};

pub struct LoopEncoder<'tcx> {
    pub loop_info: ProcedureLoops,
    /// Places that are accessed in each loop. The index of the loop
    /// head basic block is used as a key.
    pub accessed_places: HashMap<BasicBlockIndex, Vec<PlaceAccess<'tcx>>>,
}

impl<'tcx> LoopEncoder<'tcx> {

    pub fn new<'a>(mir: &'a mir::Mir<'tcx>) -> LoopEncoder<'tcx>
        where 'tcx: 'a
    {
        let loop_info = ProcedureLoops::new(mir);
        let mut accessed_places = HashMap::new();
        for &loop_head in loop_info.loop_heads.iter() {
            let accesses = loop_info.compute_used_paths(loop_head, mir);
            accessed_places.insert(loop_head, accesses);
        }
        LoopEncoder {
            loop_info: loop_info,
            accessed_places: accessed_places,
        }
    }

}
