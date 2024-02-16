use super::{
    super::transformations::{
        encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
    },
    smt::SmtSolver,
    VerificationResult, Verifier,
};
use crate::encoder::errors::SpannedEncodingResult;
use log::{debug, info};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::{
    common::{
        cfg::Cfg,
        expression::{BinaryOperationHelpers, ExpressionIterator, SyntacticEvaluation},
        graphviz::ToGraphviz,
    },
    low::{self as vir_low},
};

#[derive(Debug)]
pub struct StackFrame {
    parent: Option<vir_low::Label>,
    label: vir_low::Label,
    /// The index of the statement in the block that is currently being
    /// executed.
    statement_index: usize,
    is_executed: bool,
}

pub(super) struct ProcedureExecutor<'a, 'c, EC: EncoderContext> {
    verifier: &'a mut Verifier,
    source_filename: &'a str,
    program_context: &'a mut ProgramContext<'c, EC>,
    procedure: &'a vir_low::ProcedureDecl,
    stack: Vec<StackFrame>,
    smt_solver: SmtSolver,
}

impl<'a, 'c, EC: EncoderContext> Drop for ProcedureExecutor<'a, 'c, EC> {
    fn drop(&mut self) {
        if prusti_common::config::dump_debug_info() && std::thread::panicking() {
            // prusti_common::report::log::report_with_writer(
            //     "graphviz_method_vir_low_crashing_symbolic_execution",
            //     format!("{}.{}.crash.dot", self.source_filename, self.procedure.name,),
            //     |writer| self.to_graphviz(writer).unwrap(),
            // );
        }
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn new(
        verifier: &'a mut Verifier,
        source_filename: &'a str,
        program_context: &'a mut ProgramContext<'c, EC>,
        procedure: &'a vir_low::ProcedureDecl,
    ) -> SpannedEncodingResult<Self> {
        let smt_solver = SmtSolver::default().unwrap();
        // let result = smt_solver.check_sat().unwrap();
        // assert!(result.is_sat());
        Ok(Self {
            verifier,
            source_filename,
            program_context,
            procedure,
            stack: Vec::new(),
            smt_solver,
        })
    }

    pub(super) fn execute_procedure(mut self) -> SpannedEncodingResult<VerificationResult> {
        info!("Executing procedure: {}", self.procedure.name);
        let mut current_block = self.procedure.entry.clone();
        let frame = StackFrame {
            parent: None,
            label: current_block.clone(),
            statement_index: 0,
            is_executed: false,
        };
        self.stack.push(frame);
        while !self.stack.is_empty() {
            self.execute_block()?;
            self.execute_terminator()?;
            self.pop_executed_frames();
        }
        info!("Finished executing procedure: {}", self.procedure.name);
        unimplemented!();
    }

    fn current_frame(&self) -> &StackFrame {
        self.stack.last().unwrap()
    }

    fn current_frame_mut(&mut self) -> &mut StackFrame {
        self.stack.last_mut().unwrap()
    }

    fn current_block(&self) -> &vir_low::BasicBlock {
        self.procedure.basic_blocks.get(&self.current_frame().label).unwrap()
    }

    fn execute_block(&mut self) -> SpannedEncodingResult<()> {
        info!("Executing block: {}", self.current_frame().label);
        let frame = self.current_frame_mut();
        frame.is_executed = true;
        Ok(())
    }

    fn execute_terminator(&mut self) -> SpannedEncodingResult<()> {
        match self.current_block().successor.clone() {
            vir_low::Successor::Return => {
                info!("Executing return terminator");
                self.stack.pop();
            }
            vir_low::Successor::Goto(ref label) => {
                info!("Executing goto terminator");
                self.stack.pop();
                self.stack.push(StackFrame {
                    parent: self.current_frame().parent.clone(),
                    label: label.clone(),
                    statement_index: 0,
                    is_executed: false,
                });
            }
            vir_low::Successor::GotoSwitch(ref cases) => {
                info!("Executing switch terminator");
                for (_, label) in cases.iter().rev() {
                    let current_label = self.current_frame().label.clone();
                    self.stack.push(StackFrame {
                        parent: Some(current_label),
                        label: label.clone(),
                        statement_index: 0,
                        is_executed: false,
                    });
                }
            }
        }
        Ok(())
    }

    fn pop_executed_frames(&mut self) {
        while let Some(frame) = self.stack.last() {
            if frame.is_executed {
                self.stack.pop();
            } else {
                break;
            }
        }
    }
}
