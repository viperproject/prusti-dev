use super::{
    super::{
        super::transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
        smt::{SmtSolver, Sort2SmtWrap},
        VerificationResult, Verifier,
    },
    heap::Heap,
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
    heap: Heap,
    saved_state_labels: Vec<String>,
}

impl StackFrame {
    pub(super) fn parent(&self) -> &Option<vir_low::Label> {
        &self.parent
    }

    pub(in super::super) fn label(&self) -> &vir_low::Label {
        &self.label
    }

    pub(in super::super) fn statement_index(&self) -> usize {
        self.statement_index
    }

    pub(super) fn heap_mut(&mut self) -> &mut Heap {
        &mut self.heap
    }

    pub(super) fn heap(&self) -> &Heap {
        &self.heap
    }

    pub(super) fn log_saved_state_label(&mut self, label: String) -> SpannedEncodingResult<()> {
        self.saved_state_labels.push(label);
        Ok(())
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(in super::super) fn current_frame(&self) -> &StackFrame {
        self.stack.last().unwrap()
    }

    pub(super) fn current_frame_mut(&mut self) -> &mut StackFrame {
        self.stack.last_mut().unwrap()
    }

    pub(super) fn inc_statement_index(&mut self) -> SpannedEncodingResult<()> {
        let frame = self.current_frame_mut();
        frame.statement_index += 1;
        Ok(())
    }

    pub(super) fn stack_push(
        &mut self,
        parent: Option<vir_low::Label>,
        label: vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        let heap = if let Some(parent) = &parent {
            let frame = self
                .stack
                .iter()
                .find(|frame| frame.label() == parent)
                .unwrap();
            assert_eq!(frame.status, StackFrameStatus::Executed);
            frame.heap.clone()
        } else {
            Heap::default()
        };
        let frame = StackFrame {
            parent,
            label,
            statement_index: 0,
            status: StackFrameStatus::Created,
            heap,
            saved_state_labels: Vec::new(),
        };
        self.stack.push(frame);
        self.smt_solver.push().unwrap(); // FIXME: Handle errors
        Ok(())
    }

    pub(super) fn stack_pop(&mut self) -> SpannedEncodingResult<()> {
        let frame = self.stack.pop().unwrap();
        assert_eq!(frame.status, StackFrameStatus::Executed);
        for label in frame.saved_state_labels {
            assert!(self.saved_heaps.remove(&label).is_some());
        }
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

    pub(in super::super) fn current_execution_trace(&self) -> SpannedEncodingResult<Vec<&str>> {
        let mut trace = Vec::new();
        for frame in &self.stack {
            if matches!(frame.status, StackFrameStatus::Executed) {
                trace.push(&*frame.label.name);
            }
        }
        Ok(trace)
    }
}
