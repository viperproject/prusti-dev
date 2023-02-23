// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::mir::{AssertMessage, BasicBlock, Place, SwitchTargets};

use crate::MicroOperand;

#[derive(Clone, Debug)]
pub struct MicroTerminator<'tcx> {
    pub kind: MicroTerminatorKind<'tcx>,
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum MicroTerminatorKind<'tcx> {
    Goto {
        target: BasicBlock,
    },
    SwitchInt {
        discr: MicroOperand,
        targets: SwitchTargets,
    },
    Resume,
    Abort,
    Return,
    Unreachable,
    Drop {
        place: Place<'tcx>,
        target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    DropAndReplace {
        place: Place<'tcx>,
        value: MicroOperand,
        target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    Call {
        func: MicroOperand,
        args: Vec<MicroOperand>,
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        cleanup: Option<BasicBlock>,
        from_hir_call: bool,
        // fn_span: Span,
    },
    Assert {
        cond: MicroOperand,
        expected: bool,
        msg: AssertMessage<'tcx>,
        target: BasicBlock,
        cleanup: Option<BasicBlock>,
    },
    Yield {
        value: MicroOperand,
        resume: BasicBlock,
        resume_arg: Place<'tcx>,
        drop: Option<BasicBlock>,
    },
    GeneratorDrop,
    FalseEdge {
        real_target: BasicBlock,
        imaginary_target: BasicBlock,
    },
    FalseUnwind {
        real_target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    // InlineAsm {
    //     template: &'tcx [InlineAsmTemplatePiece],
    //     operands: Vec<InlineAsmOperand<'tcx>>,
    //     options: InlineAsmOptions,
    //     line_spans: &'tcx [Span],
    //     destination: Option<BasicBlock>,
    //     cleanup: Option<BasicBlock>,
    // },
}
