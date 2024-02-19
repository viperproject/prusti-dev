use super::{
    super::{
        super::transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
        smt::{SmtSolver, Sort2SmtWrap},
        VerificationResult, Verifier,
    },
    ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::{
    common::{
        cfg::Cfg,
        expression::{BinaryOperationHelpers, ExpressionIterator, SyntacticEvaluation},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum StackFrameStatus {
    /// The frame has been created but no statement has been executed yet.
    Created,
    /// The frame is currently being executed.
    BeingExecuted,
    /// The frame has been fully executed. However, its children may currently
    /// be executed.
    Executed,
}

#[derive(Debug)]
pub struct StackFrame {
    parent: Option<vir_low::Label>,
    label: vir_low::Label,
    /// The index of the statement in the block that is currently being
    /// executed.
    statement_index: usize,
    status: StackFrameStatus,
}

impl StackFrame {
    pub(super) fn parent(&self) -> &Option<vir_low::Label> {
        &self.parent
    }

    pub(super) fn label(&self) -> &vir_low::Label {
        &self.label
    }

    pub(super) fn statement_index(&self) -> usize {
        self.statement_index
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn current_frame(&self) -> &StackFrame {
        self.stack.last().unwrap()
    }

    pub(super) fn current_frame_mut(&mut self) -> &mut StackFrame {
        self.stack.last_mut().unwrap()
    }

    pub(super) fn stack_push(
        &mut self,
        parent: Option<vir_low::Label>,
        label: vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        let frame = StackFrame {
            parent,
            label,
            statement_index: 0,
            status: StackFrameStatus::Created,
        };
        self.stack.push(frame);
        self.smt_solver.push().unwrap(); // FIXME: Handle errors
        Ok(())
    }

    pub(super) fn stack_pop(&mut self) -> SpannedEncodingResult<()> {
        let frame = self.stack.pop().unwrap();
        assert_eq!(frame.status, StackFrameStatus::Executed);
        self.smt_solver.pop().unwrap(); // FIXME: Handle errors
        Ok(())
    }

    pub(super) fn pop_executed_frames(&mut self) -> SpannedEncodingResult<()> {
        while let Some(frame) = self.stack.last() {
            if frame.status == StackFrameStatus::Executed {
                self.stack_pop()?;
            } else {
                break;
            }
        }
        Ok(())
    }

    pub(super) fn mark_current_frame_as_being_executed(&mut self) -> SpannedEncodingResult<()> {
        let frame = self.current_frame_mut();
        assert_eq!(frame.status, StackFrameStatus::Created);
        frame.status = StackFrameStatus::BeingExecuted;
        Ok(())
    }

    pub(super) fn mark_current_frame_as_executed(&mut self) -> SpannedEncodingResult<()> {
        let frame = self.current_frame_mut();
        assert_eq!(frame.status, StackFrameStatus::BeingExecuted);
        frame.status = StackFrameStatus::Executed;
        Ok(())
    }

    pub(super) fn log_current_stack_status(&mut self) -> SpannedEncodingResult<()> {
        for frame in &self.stack {
            self.smt_solver
                .comment(&format!(
                    "Frame: {} status={:?} parent={:?}",
                    frame.label(),
                    frame.status,
                    frame.parent()
                ))
                .unwrap(); // FIXME: Handle errors
        }
        Ok(())
    }
}
