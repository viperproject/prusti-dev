// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use core::fmt::{Debug, Formatter, Result, Write};
use prusti_rustc_interface::{
    middle::mir::{AssertMessage, BasicBlock, SwitchTargets, Terminator, TerminatorKind},
    span::Span,
};
use std::{borrow::Cow, iter};

use crate::{
    permission::FreeState, MicroOperand, Operands, Place, PlaceCapabilitySummary,
    TerminatorPlaceCapabilitySummary,
};

#[derive(Clone)]
pub struct MicroTerminator<'tcx> {
    pub repack_operands: Option<PlaceCapabilitySummary<'tcx>>,
    pub operands: Operands<'tcx>,
    pub kind: MicroTerminatorKind<'tcx>,
    pub repack_join: Option<TerminatorPlaceCapabilitySummary<'tcx>>,
    // TODO: debug only
    pub previous_rjs: Vec<FreeState<'tcx>>,
    pub original_kind: TerminatorKind<'tcx>,
}

#[derive(Clone, PartialEq, Hash)]
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
                place: place.into(),
                target,
                unwind,
            },
            TerminatorKind::DropAndReplace {
                place,
                value,
                target,
                unwind,
            } => MicroTerminatorKind::DropAndReplace {
                place: (*place).into(),
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
                destination: (*destination).into(),
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
                resume_arg: (*resume_arg).into(),
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
            previous_rjs: Vec::new(),
            original_kind: term.kind.clone(),
        }
    }
}

impl<'tcx> Debug for MicroTerminator<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let mut dbg = f.debug_struct("MicroTerminator");
        if let Some(repack) = &self.repack_operands {
            dbg.field("pcs", repack);
        }
        if self.operands.len() > 0 {
            dbg.field("operands", &*self.operands);
        }
        dbg.field("term", &TermDebug(&self.kind, &self.original_kind));
        if let Some(repack) = &self.repack_join {
            dbg.field("pcs_join", repack);
        }
        dbg.finish()
    }
}

pub(crate) struct TermDebug<'a, 'tcx>(
    pub(crate) &'a MicroTerminatorKind<'tcx>,
    pub(crate) &'a TerminatorKind<'tcx>,
);
impl<'a, 'tcx> Debug for TermDebug<'a, 'tcx> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        self.0.fmt_head(fmt)?;
        let successor_count = self.1.successors().count();
        let labels = self.0.fmt_successor_labels();
        assert_eq!(successor_count, labels.len());

        match successor_count {
            0 => Ok(()),
            1 => write!(fmt, " -> {:?}", self.1.successors().next().unwrap()),
            _ => {
                write!(fmt, " -> [")?;
                for (i, target) in self.1.successors().enumerate() {
                    if i > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{}: {:?}", labels[i], target)?;
                }
                write!(fmt, "]")
            }
        }
    }
}

impl<'tcx> MicroTerminatorKind<'tcx> {
    pub fn fmt_head<W: Write>(&self, fmt: &mut W) -> Result {
        use MicroTerminatorKind::*;
        match self {
            Goto { .. } => write!(fmt, "goto"),
            SwitchInt { discr, .. } => write!(fmt, "switchInt({discr:?})"),
            Return => write!(fmt, "return"),
            GeneratorDrop => write!(fmt, "generator_drop"),
            Resume => write!(fmt, "resume"),
            Abort => write!(fmt, "abort"),
            Yield {
                value, resume_arg, ..
            } => write!(fmt, "{resume_arg:?} = yield({value:?})"),
            Unreachable => write!(fmt, "unreachable"),
            Drop { place, .. } => write!(fmt, "drop({place:?})"),
            DropAndReplace { place, value, .. } => {
                write!(fmt, "replace({place:?} <- {value:?})")
            }
            Call {
                func,
                args,
                destination,
                ..
            } => {
                write!(fmt, "{destination:?} = ")?;
                write!(fmt, "{func:?}(")?;
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{arg:?}")?;
                }
                write!(fmt, ")")
            }
            Assert {
                cond,
                expected,
                msg,
                ..
            } => {
                write!(fmt, "assert(")?;
                if !expected {
                    write!(fmt, "!")?;
                }
                write!(fmt, "{cond:?}, ")?;
                msg.fmt_assert_args(fmt)?;
                write!(fmt, ")")
            }
            FalseEdge { .. } => write!(fmt, "falseEdge"),
            FalseUnwind { .. } => write!(fmt, "falseUnwind"),
            // InlineAsm { template, ref operands, options, .. } => {
            //     write!(fmt, "asm!(\"{}\"", InlineAsmTemplatePiece::to_string(template))?;
            //     for op in operands {
            //         write!(fmt, ", ")?;
            //         let print_late = |&late| if late { "late" } else { "" };
            //         match op {
            //             InlineAsmOperand::In { reg, value } => {
            //                 write!(fmt, "in({}) {:?}", reg, value)?;
            //             }
            //             InlineAsmOperand::Out { reg, late, place: Some(place) } => {
            //                 write!(fmt, "{}out({}) {:?}", print_late(late), reg, place)?;
            //             }
            //             InlineAsmOperand::Out { reg, late, place: None } => {
            //                 write!(fmt, "{}out({}) _", print_late(late), reg)?;
            //             }
            //             InlineAsmOperand::InOut {
            //                 reg,
            //                 late,
            //                 in_value,
            //                 out_place: Some(out_place),
            //             } => {
            //                 write!(
            //                     fmt,
            //                     "in{}out({}) {:?} => {:?}",
            //                     print_late(late),
            //                     reg,
            //                     in_value,
            //                     out_place
            //                 )?;
            //             }
            //             InlineAsmOperand::InOut { reg, late, in_value, out_place: None } => {
            //                 write!(fmt, "in{}out({}) {:?} => _", print_late(late), reg, in_value)?;
            //             }
            //             InlineAsmOperand::Const { value } => {
            //                 write!(fmt, "const {:?}", value)?;
            //             }
            //             InlineAsmOperand::SymFn { value } => {
            //                 write!(fmt, "sym_fn {:?}", value)?;
            //             }
            //             InlineAsmOperand::SymStatic { def_id } => {
            //                 write!(fmt, "sym_static {:?}", def_id)?;
            //             }
            //         }
            //     }
            //     write!(fmt, ", options({:?}))", options)
            // }
        }
    }

    pub fn fmt_successor_labels(&self) -> Vec<Cow<'static, str>> {
        use MicroTerminatorKind::*;
        match *self {
            Return | Resume | Abort | Unreachable | GeneratorDrop => vec![],
            Goto { .. } => vec!["".into()],
            SwitchInt { ref targets, .. } => targets
                .iter()
                .map(|(u, _)| Cow::Owned(u.to_string()))
                .chain(iter::once("otherwise".into()))
                .collect(),
            Call {
                target: Some(_),
                cleanup: Some(_),
                ..
            } => {
                vec!["return".into(), "unwind".into()]
            }
            Call {
                target: Some(_),
                cleanup: None,
                ..
            } => vec!["return".into()],
            Call {
                target: None,
                cleanup: Some(_),
                ..
            } => vec!["unwind".into()],
            Call {
                target: None,
                cleanup: None,
                ..
            } => vec![],
            Yield { drop: Some(_), .. } => vec!["resume".into(), "drop".into()],
            Yield { drop: None, .. } => vec!["resume".into()],
            DropAndReplace { unwind: None, .. } | Drop { unwind: None, .. } => {
                vec!["return".into()]
            }
            DropAndReplace {
                unwind: Some(_), ..
            }
            | Drop {
                unwind: Some(_), ..
            } => {
                vec!["return".into(), "unwind".into()]
            }
            Assert { cleanup: None, .. } => vec!["".into()],
            Assert { .. } => vec!["success".into(), "unwind".into()],
            FalseEdge { .. } => vec!["real".into(), "imaginary".into()],
            FalseUnwind {
                unwind: Some(_), ..
            } => vec!["real".into(), "cleanup".into()],
            FalseUnwind { unwind: None, .. } => vec!["real".into()],
            // InlineAsm { destination: Some(_), cleanup: Some(_), .. } => {
            //     vec!["return".into(), "unwind".into()]
            // }
            // InlineAsm { destination: Some(_), cleanup: None, .. } => vec!["return".into()],
            // InlineAsm { destination: None, cleanup: Some(_), .. } => vec!["unwind".into()],
            // InlineAsm { destination: None, cleanup: None, .. } => vec![],
        }
    }
}
