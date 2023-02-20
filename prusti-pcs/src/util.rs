// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::PrustiError;
use prusti_rustc_interface::middle::mir::TerminatorKind;

/// Wrapper type for all errors
pub type EncodingResult<A> = Result<A, PrustiError>;

pub fn abbreviate_terminator(k: &TerminatorKind) -> &'static str {
    match k {
        TerminatorKind::Goto { .. } => "goto",
        TerminatorKind::SwitchInt { .. } => "switchint",
        TerminatorKind::Resume => "resume",
        TerminatorKind::Abort => "abort",
        TerminatorKind::Return => "return",
        TerminatorKind::Unreachable => "unreachable",
        TerminatorKind::Drop { .. } => "drop",
        TerminatorKind::DropAndReplace { .. } => "dropandreplace",
        TerminatorKind::Call { .. } => "call",
        TerminatorKind::Assert { .. } => "assert",
        TerminatorKind::Yield { .. } => "yield",
        TerminatorKind::GeneratorDrop => "generatordrop",
        TerminatorKind::FalseEdge { .. } => "falseedge",
        TerminatorKind::FalseUnwind { .. } => "falseunwind",
        TerminatorKind::InlineAsm { .. } => "inlineasm",
    }
}
