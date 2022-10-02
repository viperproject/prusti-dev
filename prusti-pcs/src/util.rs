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
        TerminatorKind::Goto { target: _ } => "goto",
        TerminatorKind::SwitchInt {
            discr: _,
            switch_ty: _,
            targets: _,
        } => "switchint",
        TerminatorKind::Resume => "resume",
        TerminatorKind::Abort => "abort",
        TerminatorKind::Return => "return",
        TerminatorKind::Unreachable => "unreachable",
        TerminatorKind::Drop {
            place: _,
            target: _,
            unwind: _,
        } => "drop",
        TerminatorKind::DropAndReplace {
            place: _,
            value: _,
            target: _,
            unwind: _,
        } => "dropandreplace",
        TerminatorKind::Call {
            func: _,
            args: _,
            destination: _,
            target: _,
            cleanup: _,
            from_hir_call: _,
            fn_span: _,
        } => "call",
        TerminatorKind::Assert {
            cond: _,
            expected: _,
            msg: _,
            target: _,
            cleanup: _,
        } => "assert",
        TerminatorKind::Yield {
            value: _,
            resume: _,
            resume_arg: _,
            drop: _,
        } => "yield",
        TerminatorKind::GeneratorDrop => "generatordrop",
        TerminatorKind::FalseEdge {
            real_target: _,
            imaginary_target: _,
        } => "falseedge",
        TerminatorKind::FalseUnwind {
            real_target: _,
            unwind: _,
        } => "falseunwind",
        TerminatorKind::InlineAsm {
            template: _,
            operands: _,
            options: _,
            line_spans: _,
            destination: _,
            cleanup: _,
        } => "inlineasm",
    }
}
