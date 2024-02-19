use self::stack::StackFrame;
use super::{
    super::transformations::{
        encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
    },
    smt::{SmtSolver, Sort2SmtWrap},
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

mod stack;
mod statements;

pub(super) struct ProcedureExecutor<'a, 'c, EC: EncoderContext> {
    verifier: &'a mut Verifier,
    source_filename: &'a str,
    program_context: &'a mut ProgramContext<'c, EC>,
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
        if !std::thread::panicking() {
            assert_eq!(self.stack.len(), 0);
        }
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn new(
        verifier: &'a mut Verifier,
        source_filename: &'a str,
        program_context: &'a mut ProgramContext<'c, EC>,
    ) -> SpannedEncodingResult<Self> {
        let smt_solver = SmtSolver::default().unwrap();
        Ok(Self {
            verifier,
            source_filename,
            program_context,
            stack: Vec::new(),
            smt_solver,
        })
    }

    pub(super) fn execute_procedure(
        mut self,
        procedure: &'a vir_low::ProcedureDecl,
    ) -> SpannedEncodingResult<VerificationResult> {
        info!("Executing procedure: {}", procedure.name);
        self.smt_solver.push().unwrap(); // FIXME: Handle errors
        self.smt_solver
            .comment(&format!("Executing procedure: {}", procedure.name))
            .unwrap(); // FIXME: Handle errors
        self.stack_push(None, procedure.entry.clone())?;
        while !self.stack.is_empty() {
            self.mark_current_frame_as_being_executed()?;
            self.log_current_stack_status()?;
            let block = procedure
                .basic_blocks
                .get(&self.current_frame().label())
                .unwrap();
            self.execute_block(block)?;
            // Executing the terminator changes the stack, so we need to mark
            // the frame as executed now.
            self.mark_current_frame_as_executed()?;
            self.execute_terminator(block)?;
            self.pop_executed_frames()?;
        }
        info!("Finished executing procedure: {}", procedure.name);
        self.smt_solver
            .comment(&format!("Finished executing procedure: {}", procedure.name))
            .unwrap(); // FIXME: Handle errors
        self.smt_solver.pop().unwrap(); // FIXME: Handle errors
        unimplemented!();
    }

    fn execute_block(&mut self, block: &vir_low::BasicBlock) -> SpannedEncodingResult<()> {
        info!("Executing block: {}", self.current_frame().label());
        let frame = self.current_frame_mut();
        for statement in &block.statements {
            self.execute_statement(statement)?;
        }
        Ok(())
    }

    fn execute_terminator(&mut self, block: &vir_low::BasicBlock) -> SpannedEncodingResult<()> {
        let current_label = self.current_frame().label().clone();
        match &block.successor {
            vir_low::Successor::Return => {
                info!("Executing return terminator");
                self.stack_pop()?;
            }
            vir_low::Successor::Goto(label) => {
                info!("Executing goto terminator");
                self.stack_push(Some(current_label), label.clone())?;
            }
            vir_low::Successor::GotoSwitch(cases) => {
                info!("Executing switch terminator");
                for (_, label) in cases.iter().rev() {
                    self.stack_push(Some(current_label.clone()), label.clone())?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn load_domains(
        &mut self,
        domains: &[vir_low::DomainDecl],
    ) -> SpannedEncodingResult<()> {
        // self.create_builtin_types()?;
        self.create_domain_types(domains)?;
        self.create_domain_functions(domains)?;
        self.define_domain_axioms(domains)?;
        assert!(self.smt_solver.check_sat().unwrap().is_sat_or_unknown());
        Ok(())
    }

    fn create_domain_types(
        &mut self,
        domains: &[vir_low::DomainDecl],
    ) -> SpannedEncodingResult<()> {
        for domain in domains {
            let domain_name = &domain.name;
            self.smt_solver.declare_sort(domain_name).unwrap(); // FIXME: Handle errors
        }
        Ok(())
    }

    fn create_domain_functions(
        &mut self,
        domains: &[vir_low::DomainDecl],
    ) -> SpannedEncodingResult<()> {
        for domain in domains {
            for function in &domain.functions {
                let parameter_types = function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.wrap())
                    .collect::<Vec<_>>();
                self.smt_solver
                    .declare_function(
                        &domain.name,
                        &function.name,
                        parameter_types,
                        function.return_type.wrap(),
                    )
                    .unwrap(); // FIXME: Handle errors
            }
        }
        Ok(())
    }

    fn define_domain_axioms(
        &mut self,
        domains: &[vir_low::DomainDecl],
    ) -> SpannedEncodingResult<()> {
        for domain in domains {
            for axiom in &domain.axioms {
                if let Some(comment) = &axiom.comment {
                    self.smt_solver.comment(comment).unwrap(); // FIXME: Handle errors
                }
                self.smt_solver
                    .comment(&format!("axiom: {}", axiom.name))
                    .unwrap(); // FIXME: Handle errors
                self.smt_solver.assert(&axiom.body).unwrap(); // FIXME: Handle errors
            }
        }
        Ok(())
    }
}
