use super::{IntoLow, State};
use crate::encoder::encoder::Encoder;
use std::collections::{HashMap, HashSet};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{ast as vir_low_ast, cfg as vir_low_cfg},
    middle::{ast as vir_mid_ast, cfg as vir_mid_cfg, operations::ty::Typed},
};

impl IntoLow<vir_low_cfg::ProcedureDecl> for vir_mid_cfg::ProcedureDecl {
    fn into_low(self, state: &mut dyn State) -> vir_low_cfg::ProcedureDecl {
        let locals = self.collect_locals().into_low(state);
        let mut basic_blocks = Vec::new();
        for (label, basic_block) in self.basic_blocks {
            let block = vir_low_cfg::BasicBlock {
                label: label.into_low(state),
                statements: basic_block
                    .statements
                    .into_iter()
                    .flat_map(|statement| statement.into_low(state))
                    .collect(),
                successor: basic_block.successor.into_low(state),
            };
            basic_blocks.push(block);
        }
        vir_low_cfg::ProcedureDecl {
            name: self.name,
            locals,
            basic_blocks,
        }
    }
}

impl IntoLow<vir_low_ast::FunctionDecl> for vir_mid_ast::FunctionDecl {
    fn into_low(self, state: &mut dyn State) -> vir_low_ast::FunctionDecl {
        vir_low_ast::FunctionDecl {
            name: self.get_identifier(),
            parameters: self.parameters.into_low(state),
            return_type: self.return_type.into_low(state),
            pres: self.pres.into_low(state),
            posts: self.posts.into_low(state),
            body: self.body.into_low(state),
        }
    }
}

impl<T, S: IntoLow<T>> IntoLow<Vec<T>> for Vec<S> {
    fn into_low(self, state: &mut dyn State) -> Vec<T> {
        self.into_iter().map(|decl| decl.into_low(state)).collect()
    }
}

impl<T, S: IntoLow<T>> IntoLow<Option<T>> for Option<S> {
    fn into_low(self, state: &mut dyn State) -> Option<T> {
        self.map(|decl| decl.into_low(state))
    }
}

impl IntoLow<vir_low_ast::variable::VariableDecl> for vir_mid_ast::variable::VariableDecl {
    fn into_low(self, state: &mut dyn State) -> vir_low_ast::variable::VariableDecl {
        vir_low_ast::variable::VariableDecl {
            name: self.name,
            ty: self.ty.into_low(state),
        }
    }
}

impl IntoLow<vir_low_ast::ty::Type> for vir_mid_ast::ty::Type {
    fn into_low(self, state: &mut dyn State) -> vir_low_ast::ty::Type {
        state.lower_type(self)
    }
}

impl IntoLow<vir_low_ast::Expression> for vir_mid_ast::Expression {
    fn into_low(self, state: &mut dyn State) -> vir_low_ast::Expression {
        state.lower_expression(self)
    }
}

impl IntoLow<Vec<vir_low_ast::statement::Statement>> for vir_mid_ast::Statement {
    fn into_low(self, state: &mut dyn State) -> Vec<vir_low_ast::statement::Statement> {
        use vir_low_ast::statement::Statement;
        match self {
            Self::Comment(statement) => {
                vec![Statement::comment(statement.comment)]
            }
            Self::Inhale(statement) => {
                vec![Statement::inhale(
                    statement.predicate.into_low(state),
                    statement.position.into(),
                )]
            }
            Self::Exhale(statement) => {
                vec![Statement::exhale(
                    statement.predicate.into_low(state),
                    statement.position.into(),
                )]
            }
            Self::MovePlace(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.source.get_type();
                assert_eq!(target_ty, source_ty);
                vec![Statement::method_call(
                    format!("move_place${}", target_ty.get_identifier()),
                    vec![
                        state.lower_expression_into_place(&statement.target),
                        state.extract_root_address(&statement.target),
                        state.lower_expression_into_snapshot(&statement.target),
                        state.lower_expression_into_place(&statement.source),
                        state.extract_root_address(&statement.source),
                        state.lower_expression_into_snapshot(&statement.source),
                    ],
                    Vec::new(),
                )]
            }
            Self::CopyPlace(_statement) => {
                unimplemented!();
            }
            Self::WritePlace(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                let root_address = state.extract_root_address(&statement.target);
                vec![Statement::method_call(
                    format!("write_place${}", target_ty.get_identifier()),
                    vec![
                        state.lower_expression_into_place(&statement.target),
                        root_address,
                        state.lower_expression_into_snapshot(&statement.value),
                    ],
                    Vec::new(),
                )]
            }
            Self::WriteAddress(statement) => {
                let target_ty = statement.target.get_type();
                let source_ty = statement.value.get_type();
                assert_eq!(target_ty, source_ty);
                vec![
                    // method write$T(address: Address, value: Snap$T)
                    //      requires MemoryBlock(address, size_of::<T>())
                    //      ensures MemoryBlock(address, size_of::<T>())
                    //      ensures MemoryBlock$bytes(address, size_of::<T>()) == Snap$T$to_bytes(value)
                    Statement::method_call(
                        format!("write_address${}", target_ty.get_identifier()),
                        vec![
                            // field_address$T$f(_1$address)
                            state
                                .lower_expression_into_place_address_computation(&statement.target),
                            // value
                            state.lower_expression_into_snapshot(&statement.value),
                        ],
                        Vec::new(),
                    ),
                ]
            }
        }
    }
}

impl IntoLow<vir_low_ast::expression::Expression> for vir_mid_ast::predicate::Predicate {
    fn into_low(self, state: &mut dyn State) -> vir_low_ast::expression::Expression {
        use vir_mid_ast::predicate::Predicate;
        match self {
            Predicate::MemoryBlockStack(predicate) => {
                vir_low_ast::Expression::predicate_access_predicate(
                    "MemoryBlockStack".to_string(),
                    vec![
                        predicate.place.into_low(state),
                        predicate.size.into_low(state),
                    ],
                    vir_low_ast::PermAmount::Write,
                    predicate.position.into(),
                )
            }
            Predicate::MemoryBlockStackDrop(predicate) => {
                vir_low_ast::Expression::predicate_access_predicate(
                    "MemoryBlockStackDrop".to_string(),
                    vec![
                        predicate.place.into_low(state),
                        predicate.size.into_low(state),
                    ],
                    vir_low_ast::PermAmount::Write,
                    predicate.position.into(),
                )
            }
            Predicate::MemoryBlockHeap(predicate) => {
                vir_low_ast::Expression::predicate_access_predicate(
                    "MemoryBlockHeap".to_string(),
                    vec![
                        predicate.address.into_low(state),
                        predicate.size.into_low(state),
                    ],
                    vir_low_ast::PermAmount::Write,
                    predicate.position.into(),
                )
            }
            Predicate::MemoryBlockHeapDrop(predicate) => {
                vir_low_ast::Expression::predicate_access_predicate(
                    "MemoryBlockHeapDrop".to_string(),
                    vec![
                        predicate.address.into_low(state),
                        predicate.size.into_low(state),
                    ],
                    vir_low_ast::PermAmount::Write,
                    predicate.position.into(),
                )
            }
        }
    }
}

impl IntoLow<vir_low_cfg::method::Label> for vir_mid_cfg::BasicBlockId {
    fn into_low(self, _state: &mut dyn State) -> vir_low_cfg::method::Label {
        vir_low_cfg::method::Label { name: self.name }
    }
}

impl IntoLow<vir_low_cfg::method::Successor> for vir_mid_cfg::Successor {
    fn into_low(self, state: &mut dyn State) -> vir_low_cfg::method::Successor {
        match self {
            vir_mid_cfg::Successor::Return => vir_low_cfg::method::Successor::Return,
            vir_mid_cfg::Successor::Goto(target) => {
                vir_low_cfg::method::Successor::Goto(target.into_low(state))
            }
            vir_mid_cfg::Successor::GotoSwitch(targets) => {
                vir_low_cfg::method::Successor::GotoSwitch(
                    targets
                        .into_iter()
                        .map(|(expression, target)| {
                            (expression.into_low(state), target.into_low(state))
                        })
                        .collect(),
                )
            }
        }
    }
}
