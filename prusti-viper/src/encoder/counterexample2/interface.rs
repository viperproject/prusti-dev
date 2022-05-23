use vir_crate::low::{self as vir_low};
use rustc_hash::{FxHashMap};
use log::{info};
//use crate::encoder::counterexample2::interface::vir_low::Expression::DomainFuncApp; //FIXME incorrrect import
//use crate::encoder::counterexample2::interface::vir_low::ast::statement::Assert; //FIXME correct import
//use crate::encoder::counterexample2::interface::vir_low::ast::statement::Assume;
//use crate::encoder::counterexample2::interface::vir_low::ast::statement::Inhale;

#[derive(Default)]
pub(crate) struct MirProcedureMapping {
    mapping: FxHashMap<String, Vec<BasicBlock>> //Map of all variables assigned in this basic block
}

/*pub(crate) struct Procedure{
    pub(crate) basic_blocks: Vec<BasicBlock>
}*/
#[derive(Debug)]
pub(crate) struct BasicBlock {
    //2 options to store labels:
    //either here for all procedures, drawback store for all procedures even if they don't have fail
    //or in silicon_counterexample_refactored line 101 //would need a new method in silicon because the current has a lot of unnecessary overhead
    pub(crate) label: String, 

    pub(crate) successor: Vec<String>,
    pub(crate) stmts: Vec<vir_low::Statement>,
    //pub(crate) inhale_stmt: Vec<Inhale>, //not implemented at the moment, only needed if snapshot var can be assign via an Inhale Statement
    //pub(crate) assert_stmt: Vec<Assert>, 
}

impl MirProcedureMapping{
    fn translate_procedure_decl(&mut self, procedure: &vir_low::ProcedureDecl) -> Vec<BasicBlock>{        
        procedure.basic_blocks.iter().map(
            | basic_block | {
                let mut stmts = Vec::new();

                for statement in &basic_block.statements{
                    match &statement {
                        vir_low::Statement::Assume(_) |
                        vir_low::Statement::Assert(_) => stmts.push(statement.clone()),
                        vir_low::Statement::Inhale(inhale) => {
                            if basic_block.label.name == "start_label" { //extract the parameter
                                info!("start_label");
                                if let Some(assume_stmt) = self.extract_param(&inhale.expression){
                                    stmts.push(assume_stmt);
                                }
                            }
                            //stmts.push(vir_low::Statement::Inhale(inhale.clone()))
                        },
                        //vir_low::Statement::Assert(assert) => stmts.push(vir_low::Statement::Assert(assert.clone())),
                        _ => (),
                     };
                }
                let successor = match &basic_block.successor{
                    vir_low::Successor::Return => Vec::new(),
                    vir_low::Successor::Goto(label) => vec![label.name.clone()],
                    vir_low::Successor::GotoSwitch(labels) => { 
                            labels.iter().map(
                                | (_, label) | 
                                label.name.clone()
                            ).collect()
                    }
                };
                let new_block = BasicBlock{
                    label: basic_block.label.name.clone(),
                    successor,
                    stmts,
                };
                info!("New block: {:?}", new_block);
                new_block
            }
        ).collect::<Vec<BasicBlock>>()
    }
    fn extract_param (&self, expression: &vir_low::Expression) -> Option<vir_low::Statement>{
         match &expression {
            vir_low::Expression::PredicateAccessPredicate(predicate_access_predicate) => {
                if predicate_access_predicate.name.contains("OwnedNonAliased$"){
                    return match predicate_access_predicate.arguments.get(2) {
                        Some(vir_low::Expression::Local(local)) => 
                            Some(vir_low::Statement::Assume(vir_low::ast::statement::Assume{
                            expression: vir_low::Expression::Local(local.clone()),
                            position: Default::default(),
                        })), 
                        _ => None,
                    }
                }
                None
            },
            vir_low::Expression::BinaryOp(binary_op) => self.extract_param(&binary_op.left),
            _ => None, 
         }
    }
}


pub(crate) trait  MirProcedureMappingInterface {
    fn add_mapping(&mut self, program: &vir_low::Program);
    fn get_mapping(&self, proc_name: String) -> Option<&Vec<BasicBlock>>;
}

impl<'v, 'tcx: 'v> MirProcedureMappingInterface for super::super::Encoder<'v, 'tcx> {
    fn add_mapping(&mut self, program: &vir_low::Program) {
        //let mut mapping = FxHashMap::default();
        if let Some(vir_low_procedure) = program.procedures.first(){
            let procedure_new = self.mir_procedure_mapping.translate_procedure_decl(vir_low_procedure);
            self.mir_procedure_mapping.mapping.insert(program.name.clone(), procedure_new);
        }
    }
    fn get_mapping(&self, proc_name: String) -> Option<&Vec<BasicBlock>>{
        self.mir_procedure_mapping.mapping.get(&proc_name)
    }
}