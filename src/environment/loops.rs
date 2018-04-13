// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use environment::procedure::{BasicBlockIndex, BasicBlockData, Procedure};
use rustc_data_structures::control_flow_graph::dominators::Dominators;
use rustc::mir;
use rustc::mir::visit::Visitor;

/// A visitor that collects the loop heads.
struct LoopHeadCollector<'d> {
    pub loop_heads: Vec<BasicBlockIndex>,
    pub dominators: &'d Dominators<BasicBlockIndex>,
}

impl<'d, 'tcx> Visitor<'tcx> for LoopHeadCollector<'d> {

    fn visit_terminator_kind(
        &mut self,
        block: BasicBlockIndex,
        kind: &mir::TerminatorKind<'tcx>,
        _: mir::Location) {
        for successor in kind.successors().iter() {
            if self.dominators.is_dominated_by(block, *successor) {
                self.loop_heads.push(*successor);
                debug!("Loop head: {:?}", successor);
            }
        }
    }

}

/// Struct that contains information about all loops in the procedure.
pub struct ProcedureLoops {
    /// A list of basic blocks that are loop heads.
    loop_heads: Vec<BasicBlockIndex>,
    /// Dominators graph.
    dominators: Dominators<BasicBlockIndex>,
}

impl ProcedureLoops {

    pub fn new<'a, 'tcx: 'a>(mir: &'a mir::Mir<'tcx>) -> ProcedureLoops {
        let dominators = mir.dominators();
        let mut loop_heads;
        {
            let mut visitor = LoopHeadCollector {
                loop_heads: Vec::new(),
                dominators: &dominators,
            };
            visitor.visit_mir(mir);
            loop_heads = visitor.loop_heads;
        }
        loop_heads.sort_unstable();
        loop_heads.dedup();
        ProcedureLoops {
            loop_heads: loop_heads,
            dominators: dominators,
        }
    }
}
