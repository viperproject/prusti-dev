use prusti_interface::data::ProcedureDefId;
use rustc_hash::FxHashMap;
use vir_crate::low::{self as vir_low};

#[derive(Default)]
pub(crate) struct MirProcedureMapping {
    //Map of all variables assigned in this basic block
    mapping: FxHashMap<ProcedureDefId, Vec<BasicBlock>>,
}

#[derive(Debug)]
pub(crate) struct BasicBlock {
    pub(crate) label: String,
    pub(crate) successor: Vec<String>,
    pub(crate) stmts: Vec<vir_low::Statement>,
}

impl MirProcedureMapping {
    ///Copies all relevant statements of a procedure for a counterexample.
    /// This is done before the verification process
    fn translate_procedure_decl(&mut self, procedure: &vir_low::ProcedureDecl) -> Vec<BasicBlock> {
        procedure
            .basic_blocks
            .iter()
            .map(|(label, basic_block)| {
                let mut stmts = Vec::new();

                for statement in &basic_block.statements {
                    match &statement {
                        vir_low::Statement::Assume(_) | vir_low::Statement::Assert(_) => {
                            stmts.push(statement.clone())
                        } //all statements that could be relevant for variable assignments
                        vir_low::Statement::Inhale(inhale) => {
                            //all statements that could be relevant for pure function calls
                            if let Some(assume_stmt) =
                                Self::extract_domain_functions(&inhale.expression)
                            {
                                stmts.push(assume_stmt);
                            }
                        }
                        _ => (),
                    };
                }
                let successor = match &basic_block.successor {
                    vir_low::Successor::Return => Vec::new(),
                    vir_low::Successor::Goto(label) => vec![label.name.clone()],
                    vir_low::Successor::GotoSwitch(labels) => {
                        labels.iter().map(|(_, label)| label.name.clone()).collect()
                    }
                };
                BasicBlock {
                    label: label.name.clone(),
                    successor,
                    stmts,
                }
            })
            .collect::<Vec<BasicBlock>>()
    }
    fn extract_domain_functions(expression: &vir_low::Expression) -> Option<vir_low::Statement> {
        // pure function all called in the following form in Viper:
        //inhale destructor_Bool(constructor_Bool_EqCmp_*(snapvar_1 caller_for$m_foo$(snapvar_2)))
        match &expression {
            vir_low::Expression::BinaryOp(binary_op) => {
                Self::extract_domain_functions(&binary_op.right)
            }
            vir_low::Expression::DomainFuncApp(domain_function_call) => {
                if domain_function_call.function_name.contains("valid$") {
                    if let Some(local) = domain_function_call.arguments.first() {
                        return Some(vir_low::Statement::Assume(
                            vir_low::ast::statement::Assume {
                                expression: local.clone(),
                                position: Default::default(),
                            },
                        ));
                    }
                }
                None
            }
            _ => None,
        }
    }
}

pub(crate) trait MirProcedureMappingInterface {
    fn add_mapping(&mut self, proc_def_id: ProcedureDefId, program: &vir_low::Program);
    fn get_mapping(&self, def_id: ProcedureDefId) -> Option<&Vec<BasicBlock>>;
}

impl<'v, 'tcx: 'v> MirProcedureMappingInterface for super::super::Encoder<'v, 'tcx> {
    fn add_mapping(&mut self, proc_def_id: ProcedureDefId, program: &vir_low::Program) {
        if let Some(vir_low_procedure) = program.procedures.first() {
            //at the moment a counterexample is only produced for the specifications-poof
            if program.check_mode.check_specifications()
            // matches!(program.check_mode, CheckMode::Specifications)
            //     || matches!(program.check_mode, CheckMode::Both)
            {
                let procedure_new = self
                    .mir_procedure_mapping
                    .translate_procedure_decl(vir_low_procedure);
                // FIXME: `proc_def_id` is not unique. We should use program
                // + procedure name here instead. However, this requires
                // refactoring all code to include this information for all
                // positions.
                self.mir_procedure_mapping
                    .mapping
                    .insert(proc_def_id, procedure_new);
            }
        }
    }
    fn get_mapping(&self, def_id: ProcedureDefId) -> Option<&Vec<BasicBlock>> {
        self.mir_procedure_mapping.mapping.get(&def_id)
    }
}
