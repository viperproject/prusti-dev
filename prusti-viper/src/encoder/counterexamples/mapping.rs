use super::interface::MirProcedureMappingInterface;
use crate::encoder::{errors::PositionManager, Encoder};
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::errors::MultiSpan;
use rustc_hash::FxHashMap;
use vir_crate::low::{self as vir_low};
use vir_low::ast::{
    expression::{BinaryOp, BinaryOpKind, ContainerOp, ContainerOpKind, DomainFuncApp, FuncApp},
    statement::Assume,
};

#[derive(Default)]
pub(crate) struct VarMapping {
    //Mapping between mir varable names and basic blocks of snapshotvariables
    pub(crate) var_snaphot_mapping: FxHashMap<String, FxHashMap<String, Vec<SnapshotVar>>>,
    //Mapping of all labels and its successors label
    pub(crate) labels_successor_mapping: FxHashMap<String, Vec<String>>,
    //Mapping of pure function calls per basic block
    pub(crate) pure_functions_mapping: FxHashMap<String, Vec<PureFunction>>,
}

#[derive(Debug)]
pub(crate) struct SnapshotVar {
    pub(crate) name: String,
    pub(crate) position: vir_low::Position,
}

#[derive(Debug)]
pub(crate) struct PureFunction {
    pub(crate) name: String,
    pub(crate) args: Vec<String>,
    pub(crate) position: vir_low::Position,
}

pub(crate) trait VarMappingInterface {
    fn create_mapping(&mut self, def_id: ProcedureDefId, encoder: &Encoder);
    fn get_successor(
        &self,
        label: &str,
        label_markers: &FxHashMap<String, bool>,
    ) -> Option<&String>;
    fn get_span(
        &self,
        position_manager: &PositionManager,
        position: &vir_low::Position,
    ) -> MultiSpan;
    fn extract_var_from_assume(&self, statement: &Assume) -> Option<SnapshotVar>;
    fn extract_pure_fn_from_assume(&self, statement: &Assume) -> Option<PureFunction>;
}

impl<'ce, 'tcx, 'v> VarMappingInterface
    for super::counterexample_translation_refactored::CounterexampleTranslator<'ce, 'tcx, 'v>
{
    fn create_mapping(&mut self, proc_def_id: ProcedureDefId, encoder: &Encoder) {
        if let Some(mir_procedure_mapping) = encoder.get_mapping(proc_def_id) {
            for basic_block in mir_procedure_mapping {
                let label = &basic_block.label;

                self.var_mapping
                    .labels_successor_mapping
                    .insert(label.clone(), basic_block.successor.clone());
                for statement in &basic_block.stmts {
                    let snapshot_var_option = match statement {
                        vir_low::Statement::Assume(assume) => self.extract_var_from_assume(assume),
                        _ => None,
                    };

                    if let Some(snapshot_var) = snapshot_var_option {
                        let mir_var = snapshot_var.name.split_once('$').unwrap().0.to_string();
                        match self.var_mapping.var_snaphot_mapping.get_mut(&mir_var) {
                            Some(label_snapshot_mapping) => {
                                //mir var already in mapping
                                match label_snapshot_mapping.get_mut(label) {
                                    //other snapshot vars are in mapping for that label
                                    Some(snapshot_var_vec) => {
                                        //filter duplicates
                                        if !position_equality(
                                            &snapshot_var_vec.last().unwrap().position,
                                            &snapshot_var.position,
                                        ) {
                                            //safe because vec.len => 1
                                            snapshot_var_vec.push(snapshot_var);
                                        }
                                    }
                                    None => {
                                        //no snapshot vars in mapping for that label
                                        let snapshot_var_vec = vec![snapshot_var];
                                        label_snapshot_mapping
                                            .insert(label.clone(), snapshot_var_vec);
                                    }
                                }
                            }
                            None => {
                                //mir var not in mapping
                                let snapshot_var_vec = vec![snapshot_var];
                                let mut label_snapshot_mapping = FxHashMap::default();
                                label_snapshot_mapping.insert(label.clone(), snapshot_var_vec);
                                self.var_mapping
                                    .var_snaphot_mapping
                                    .insert(mir_var, label_snapshot_mapping);
                            }
                        }
                    }

                    let pure_fn_option = match statement {
                        vir_low::Statement::Assume(assume) => {
                            self.extract_pure_fn_from_assume(assume)
                        }
                        _ => None,
                    };

                    if let Some(pure_fn) = pure_fn_option {
                        match self.var_mapping.pure_functions_mapping.get_mut(label) {
                            Some(pure_fn_vec) => {
                                //further function calls
                                pure_fn_vec.push(pure_fn);
                            }
                            None => {
                                //first function call at that label
                                let pure_fn_vec = vec![pure_fn];
                                self.var_mapping
                                    .pure_functions_mapping
                                    .insert(label.clone(), pure_fn_vec);
                            }
                        }
                    }
                }
            }
        }
    }

    ///Given a counterexample (label_markers) and a label, it returns the sucessor
    /// There can be at most 1 successor
    fn get_successor(
        &self,
        label: &str,
        label_markers: &FxHashMap<String, bool>,
    ) -> Option<&String> {
        match self.var_mapping.labels_successor_mapping.get(label) {
            Some(possible_successors) => {
                let successor = possible_successors
                    .iter()
                    .filter(|x| *label_markers.get(*x).unwrap_or(&false))
                    .collect::<Vec<&String>>();
                if successor.len() == 1 {
                    //there should always be at most one successor
                    Some(successor.first()?)
                } else {
                    //the block has no successor; end of method or verification failure in that block
                    //multiple succesors should not be possible
                    None
                }
            }
            None => None,
        }
    }
    fn get_span(
        &self,
        position_manager: &PositionManager,
        position: &vir_low::Position,
    ) -> MultiSpan {
        position_manager
            .source_span
            .get(&position.id)
            .unwrap()
            .clone() //there is always a span available
    }
    ///extract necessary information from pure function calls for counterexamples
    fn extract_pure_fn_from_assume(&self, statement: &Assume) -> Option<PureFunction> {
        //pure functions are called in the following form:
        //inhale destructor$Snap$Bool$$value(constructor$Snap$Bool$EqCmp_*(snap_var_1, caller_for$m_foo$(snap_var_1)))
        match &statement.expression {
            vir_low::Expression::DomainFuncApp(DomainFuncApp {
                domain_name: _,
                arguments,
                ..
            }) => {
                if arguments.len() == 1 || arguments.len() == 2 {
                    // might be a pure function call
                    return self.extract_pure_fn_from_assume(&Assume {
                        expression: arguments.last().unwrap().clone(),
                        position: vir_low::Position::default(),
                    });
                }
                None
            }
            vir_low::Expression::FuncApp(FuncApp {
                function_name,
                arguments,
                position,
                ..
            }) => {
                if function_name.contains("caller_for$") {
                    let args = arguments
                        .iter()
                        .filter_map(|arg| {
                            self.extract_var_from_assume(&Assume {
                                expression: arg.clone(),
                                position: vir_low::Position::default(),
                            })
                            .map(|x| x.name)
                        })
                        .collect();
                    return Some(PureFunction {
                        name: function_name.clone(),
                        args,
                        position: *position,
                    });
                }
                None
            }
            _ => None,
        }
    }

    ///extract necessary information from snapshot variables for counterexamples
    fn extract_var_from_assume(&self, statement: &Assume) -> Option<SnapshotVar> {
        //
        match &statement.expression {
            //variable assignment of the following form:
            //inhale snapvar_1 == snapvar_2
            //inhale snapvar_1[0] == snapvar_2
            vir_low::Expression::Local(local)
            | vir_low::Expression::BinaryOp(BinaryOp {
                op_kind: BinaryOpKind::EqCmp,
                left: box vir_low::Expression::Local(local),
                ..
            }) => {
                if local.variable.name.contains("snapshot") {
                    Some(SnapshotVar {
                        name: local.variable.name.clone(),
                        position: local.position,
                    })
                } else {
                    None
                }
            }
            vir_low::Expression::BinaryOp(BinaryOp {
                op_kind: BinaryOpKind::EqCmp,
                left:
                    box vir_low::Expression::ContainerOp(ContainerOp {
                        kind: ContainerOpKind::SeqIndex,
                        operands,
                        ..
                    }),
                ..
            }) => {
                if let Some(vir_low::Expression::Local(local)) = operands.first() {
                    if local.variable.name.contains("snapshot") {
                        Some(SnapshotVar {
                            name: local.variable.name.clone(),
                            position: local.position,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            //variable assignments of the following form:
            //inhale destruct_field(_1$snapshot$1) == snapvar_2                     (structs and enums)
            //inhale destruct_field_value(destruct_field(_1$snapshot$1)) == snapvar_2     (unions)
            vir_low::Expression::DomainFuncApp(DomainFuncApp {
                domain_name: _,
                function_name,
                arguments,
                ..
            })
            | vir_low::Expression::BinaryOp(BinaryOp {
                op_kind: BinaryOpKind::EqCmp,
                left:
                    box vir_low::Expression::DomainFuncApp(DomainFuncApp {
                        domain_name: _,
                        function_name,
                        arguments,
                        ..
                    }),
                ..
            }) => {
                if arguments.len() == 1
                    && (function_name.contains("target_current")
                        || function_name.contains("destructor"))
                {
                    match arguments.first().unwrap() {
                        vir_low::Expression::Local(_) | vir_low::Expression::DomainFuncApp(_) => {
                            return self.extract_var_from_assume(&Assume {
                                expression: arguments.first().unwrap().clone(),
                                position: vir_low::Position::default(),
                            })
                        }
                        _ => (),
                    }
                }

                None
            }
            _ => None,
        }
    }
}

fn position_equality(p1: &vir_low::Position, p2: &vir_low::Position) -> bool {
    p1.line == p2.line && p1.column == p2.column
}
