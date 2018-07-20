// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::mir_interpreter::{BackwardMirInterpreter, run_backward_interpretation};
use encoder::vir;
use rustc::mir;
use rustc::ty;
use prusti_interface::data::ProcedureDefId;
use std::collections::HashMap;
use prusti_interface::environment::Environment;

pub struct PureFunctionEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    mir: &'p mir::Mir<'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, proc_def_id: ProcedureDefId, mir: &'p mir::Mir<'tcx>) -> Self {
        trace!("PureFunctionEncoder constructor");
        PureFunctionEncoder {
            encoder,
            proc_def_id,
            mir,
        }
    }

    pub fn encode_body(&self) -> vir::Expr {
        trace!("encode_body");
        let interpreter = PureFunctionInterpreter::new(self.encoder, self.mir);
        let state = run_backward_interpretation(self.mir, &interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));
        state.into_expression()
    }
}

#[derive(Clone, Debug)]
struct PureFunctionState {
    expr: vir::Expr
}

impl PureFunctionState {
    fn new(expr: vir::Expr) -> Self {
        PureFunctionState {
            expr
        }
    }

    fn into_expression(self) -> vir::Expr {
        self.expr
    }
}


struct PureFunctionInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        PureFunctionInterpreter {
            encoder,
            mir
        }
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> BackwardMirInterpreter<'tcx> for PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = PureFunctionState;

    fn apply_terminator(&self, term: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Self::State {
        debug!("apply_terminator {:?}, states: {:?}", term, states);
        use rustc::mir::TerminatorKind;

        match term.kind {
            TerminatorKind::Return => {
                assert!(states.is_empty());
                let return_type = self.encoder.encode_type(self.mir.return_ty());
                let return_var = vir::LocalVar::new("_0", return_type);
                PureFunctionState::new(return_var.into())
            }

            TerminatorKind::Goto { ref target } => {
                assert_eq!(states.len(), 1);
                states[target].clone()
            }

            TerminatorKind::FalseEdges { ref real_target, .. } |
            TerminatorKind::FalseUnwind { ref real_target, .. } => {
                assert_eq!(states.len(), 1);
                states[real_target].clone()
            }

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                unimplemented!();
            }

            TerminatorKind::Unreachable |
            TerminatorKind::Abort |
            TerminatorKind::Drop{..} => {
                unreachable!()
            }

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                unimplemented!();
            }

            TerminatorKind::Call {
                ref args,
                ref destination,
                func: mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: ty::Const {
                                ty: &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ..),
                                    ..
                                },
                                ..
                            }
                        },
                        ..
                    }
                ),
                ..
            } => {
                let func_proc_name: &str = &self.encoder.env().get_item_name(def_id);
                match func_proc_name {
                    "prusti_contracts::internal::old" => {
                        debug!("Encoding old expression");
                        unimplemented!();
                    }

                    // generic function call
                    _ => {
                        debug!("Encoding function call '{}'", func_proc_name);
                        unimplemented!();
                    }
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                unimplemented!();
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    fn apply_statement(&self, stmt: &mir::Statement<'tcx>, state: &mut Self::State) {
        debug!("apply_statement {:?}, state: {:?}", stmt, state);
    }
}
