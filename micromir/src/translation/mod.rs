// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::mir::{BasicBlockData, Body, Statement, Terminator};

use crate::{MicroBasicBlockData, MicroBasicBlocks, MicroStatement, MicroTerminator};

pub(crate) fn translate_bbs<'tcx>(body: &Body<'tcx>) -> MicroBasicBlocks<'tcx> {
    println!("body: {body:#?}");
    MicroBasicBlocks {
        basic_blocks: body.basic_blocks.iter().map(translate_bb).collect(),
    }
}

pub(crate) fn translate_bb<'tcx>(data: &BasicBlockData<'tcx>) -> MicroBasicBlockData<'tcx> {
    MicroBasicBlockData {
        statements: data.statements.iter().map(translate_stmt).collect(),
        terminator: data.terminator.as_ref().map(translate_term),
        is_cleanup: data.is_cleanup,
    }
}

pub(crate) fn translate_stmt<'tcx>(_stmt: &Statement<'tcx>) -> MicroStatement<'tcx> {
    todo!()
    // let kind = match &stmt.kind {
    //     StatementKind::Assign(box (p, r)) =>
    //         MicroStatementKind::Assign(box (*p, r.clone())),
    //     StatementKind::FakeRead(box (c, p)) => MicroStatementKind::FakeRead(box (*c, *p)),
    //     StatementKind::SetDiscriminant {
    //         place,
    //         variant_index,
    //     } => MicroStatementKind::SetDiscriminant {
    //         place: box **place,
    //         variant_index: *variant_index,
    //     },
    //     StatementKind::Deinit(box p) => MicroStatementKind::Deinit(box *p),
    //     StatementKind::StorageLive(l) => MicroStatementKind::StorageLive(*l),
    //     StatementKind::StorageDead(l) => MicroStatementKind::StorageDead(*l),
    //     StatementKind::Retag(k, box p) => MicroStatementKind::Retag(*k, box *p),
    //     StatementKind::AscribeUserType(box (p, ty), v) => {
    //         MicroStatementKind::AscribeUserType(box (*p, ty.clone()), *v)
    //     }
    //     StatementKind::Coverage(box c) => MicroStatementKind::Coverage(box c.clone()),
    //     StatementKind::Intrinsic(box i) => MicroStatementKind::Intrinsic(box i.clone()),
    //     StatementKind::Nop => MicroStatementKind::Nop,
    // };
    // MicroStatement { operands: IndexVec::new(), kind }
}

pub(crate) fn translate_term<'tcx>(_term: &Terminator<'tcx>) -> MicroTerminator<'tcx> {
    todo!()
    // let kind = match &term.kind {
    //     &TerminatorKind::Goto { target } => MicroTerminatorKind::Goto { target },
    //     TerminatorKind::SwitchInt { discr, targets } => MicroTerminatorKind::SwitchInt {
    //         discr: discr.clone(),
    //         targets: targets.clone(),
    //     },
    //     TerminatorKind::Resume => MicroTerminatorKind::Resume,
    //     TerminatorKind::Abort => MicroTerminatorKind::Abort,
    //     TerminatorKind::Return => MicroTerminatorKind::Return,
    //     TerminatorKind::Unreachable => MicroTerminatorKind::Unreachable,
    //     &TerminatorKind::Drop {
    //         place,
    //         target,
    //         unwind,
    //     } => MicroTerminatorKind::Drop {
    //         place,
    //         target,
    //         unwind,
    //     },
    //     TerminatorKind::DropAndReplace {
    //         place,
    //         value,
    //         target,
    //         unwind,
    //     } => MicroTerminatorKind::DropAndReplace {
    //         place: *place,
    //         value: value.clone(),
    //         target: *target,
    //         unwind: *unwind,
    //     },
    //     TerminatorKind::Call {
    //         func,
    //         args,
    //         destination,
    //         target,
    //         cleanup,
    //         from_hir_call,
    //         fn_span: _,
    //     } => MicroTerminatorKind::Call {
    //         func: func.clone(),
    //         args: args.clone(),
    //         destination: *destination,
    //         target: *target,
    //         cleanup: *cleanup,
    //         from_hir_call: *from_hir_call,
    //         // fn_span: *fn_span,
    //     },
    //     TerminatorKind::Assert {
    //         cond,
    //         expected,
    //         msg,
    //         target,
    //         cleanup,
    //     } => MicroTerminatorKind::Assert {
    //         cond: cond.clone(),
    //         expected: *expected,
    //         msg: msg.clone(),
    //         target: *target,
    //         cleanup: *cleanup,
    //     },
    //     TerminatorKind::Yield {
    //         value,
    //         resume,
    //         resume_arg,
    //         drop,
    //     } => MicroTerminatorKind::Yield {
    //         value: value.clone(),
    //         resume: *resume,
    //         resume_arg: *resume_arg,
    //         drop: *drop,
    //     },
    //     TerminatorKind::GeneratorDrop => MicroTerminatorKind::GeneratorDrop,
    //     &TerminatorKind::FalseEdge {
    //         real_target,
    //         imaginary_target,
    //     } => MicroTerminatorKind::FalseEdge {
    //         real_target,
    //         imaginary_target,
    //     },
    //     &TerminatorKind::FalseUnwind {
    //         real_target,
    //         unwind,
    //     } => MicroTerminatorKind::FalseUnwind {
    //         real_target,
    //         unwind,
    //     },
    //     TerminatorKind::InlineAsm { .. } => todo!(),
    // };
    // MicroTerminator { kind }
}
