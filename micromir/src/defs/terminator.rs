// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    middle::mir::{AssertMessage, BasicBlock, Place, SwitchTargets, Terminator, TerminatorKind},
    span::Span,
};

use crate::{MicroOperand, Operands, PlaceCapabilitySummary};

#[derive(Clone, Debug)]
pub struct MicroTerminator<'tcx> {
    pub repack_operands: Option<PlaceCapabilitySummary<'tcx>>,
    pub operands: Operands<'tcx>,
    pub kind: MicroTerminatorKind<'tcx>,
    pub repack_join: Option<PlaceCapabilitySummary<'tcx>>,
    pub original_kind: TerminatorKind<'tcx>,
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
        fn_span: Span,
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

impl<'tcx> From<&Terminator<'tcx>> for MicroTerminator<'tcx> {
    fn from(term: &Terminator<'tcx>) -> Self {
        let mut operands = Operands::new();
        let kind = match &term.kind {
            &TerminatorKind::Goto { target } => MicroTerminatorKind::Goto { target },
            TerminatorKind::SwitchInt { discr, targets } => MicroTerminatorKind::SwitchInt {
                discr: operands.translate_operand(discr),
                targets: targets.clone(),
            },
            TerminatorKind::Resume => MicroTerminatorKind::Resume,
            TerminatorKind::Abort => MicroTerminatorKind::Abort,
            TerminatorKind::Return => MicroTerminatorKind::Return,
            TerminatorKind::Unreachable => MicroTerminatorKind::Unreachable,
            &TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => MicroTerminatorKind::Drop {
                place,
                target,
                unwind,
            },
            TerminatorKind::DropAndReplace {
                place,
                value,
                target,
                unwind,
            } => MicroTerminatorKind::DropAndReplace {
                place: *place,
                value: operands.translate_operand(value),
                target: *target,
                unwind: *unwind,
            },
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                cleanup,
                from_hir_call,
                fn_span,
            } => MicroTerminatorKind::Call {
                func: operands.translate_operand(func),
                args: args.iter().map(|a| operands.translate_operand(a)).collect(),
                destination: *destination,
                target: *target,
                cleanup: *cleanup,
                from_hir_call: *from_hir_call,
                fn_span: *fn_span,
            },
            TerminatorKind::Assert {
                cond,
                expected,
                msg,
                target,
                cleanup,
            } => MicroTerminatorKind::Assert {
                cond: operands.translate_operand(cond),
                expected: *expected,
                msg: msg.clone(),
                target: *target,
                cleanup: *cleanup,
            },
            TerminatorKind::Yield {
                value,
                resume,
                resume_arg,
                drop,
            } => MicroTerminatorKind::Yield {
                value: operands.translate_operand(value),
                resume: *resume,
                resume_arg: *resume_arg,
                drop: *drop,
            },
            TerminatorKind::GeneratorDrop => MicroTerminatorKind::GeneratorDrop,
            &TerminatorKind::FalseEdge {
                real_target,
                imaginary_target,
            } => MicroTerminatorKind::FalseEdge {
                real_target,
                imaginary_target,
            },
            &TerminatorKind::FalseUnwind {
                real_target,
                unwind,
            } => MicroTerminatorKind::FalseUnwind {
                real_target,
                unwind,
            },
            TerminatorKind::InlineAsm { .. } => todo!(),
        };
        MicroTerminator {
            repack_operands: None,
            operands,
            kind,
            repack_join: None,
            original_kind: term.kind.clone(),
        }
    }
}
