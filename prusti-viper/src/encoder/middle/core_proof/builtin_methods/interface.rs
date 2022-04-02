use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::split_join::SplitJoinHelper,
        compute_address::ComputeAddressInterface,
        errors::ErrorsInterface,
        fold_unfold::FoldUnfoldInterface,
        lifetimes::LifetimesInterface,
        lowerer::{
            Lowerer, MethodsLowererInterface, PredicatesLowererInterface, VariablesLowererInterface,
        },
        places::PlacesInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoProcedureSnapshot, IntoSnapshot, SnapshotBytesInterface, SnapshotValidityInterface,
            SnapshotValuesInterface, SnapshotVariablesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, UnaryOperationHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

#[derive(Default)]
pub(in super::super) struct BuiltinMethodsState {
    encoded_write_place_methods: FxHashSet<vir_mid::Type>,
    encoded_move_place_methods: FxHashSet<vir_mid::Type>,
    encoded_copy_place_methods: FxHashSet<vir_mid::Type>,
    encoded_write_address_methods: FxHashSet<vir_mid::Type>,
    encoded_memory_block_split_methods: FxHashSet<vir_mid::Type>,
    encoded_memory_block_join_methods: FxHashSet<vir_mid::Type>,
    encoded_into_memory_block_methods: FxHashSet<vir_mid::Type>,
    encoded_assign_methods: FxHashSet<String>,
    encoded_consume_operand_methods: FxHashSet<String>,
    encoded_newlft_method: bool,
    encoded_endlft_method: bool,
    encoded_lft_tok_sep_take_methods: FxHashSet<usize>,
    encoded_lft_tok_sep_return_methods: FxHashSet<usize>,
    encoded_open_close_mut_ref_methods: FxHashSet<vir_mid::Type>,
}

trait Private {
    fn encode_rvalue_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()>;
    fn encode_operand_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<()>;
    fn encode_place_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_tok_sep_take_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String>;
    fn encode_lft_tok_sep_return_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String>;
    fn encode_assign_method_name(
        &self,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<String>;
    fn encode_consume_operand_method_name(
        &self,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<String>;
    fn encode_assign_method(
        &mut self,
        method_name: &str,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()>;
    fn encode_consume_operand_method(
        &mut self,
        method_name: &str,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::Rvalue,
        result_type: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue_checked_binary_op(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::ast::rvalue::CheckedBinaryOp,
        ty: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue_ref(
        &mut self,
        method_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        pres: Vec<vir_low::Expression>,
        posts: Vec<vir_low::Expression>,
        value: &vir_mid::ast::rvalue::Ref,
        ty: &vir_mid::Type,
        result_value: vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_operand(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_assign_operand_place(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_assign_operand_address(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_assign_operand_snapshot(
        &mut self,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_rvalue_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()> {
        match value {
            vir_mid::Rvalue::Ref(value) => {
                self.encode_place_arguments(arguments, &value.place)?;
                let lifetime = self.encode_lifetime_const_into_variable(value.lifetime.clone())?;
                arguments.push(lifetime.into());
                let perm_amount = vir_low::Expression::fractional_permission(value.rd_perm);
                arguments.push(perm_amount);
            }
            vir_mid::Rvalue::AddressOf(value) => {
                self.encode_place_arguments(arguments, &value.place)?;
            }
            vir_mid::Rvalue::UnaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.argument)?;
            }
            vir_mid::Rvalue::BinaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.left)?;
                self.encode_operand_arguments(arguments, &value.right)?;
            }
            vir_mid::Rvalue::CheckedBinaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.left)?;
                self.encode_operand_arguments(arguments, &value.right)?;
            }
            vir_mid::Rvalue::Discriminant(value) => {
                self.encode_place_arguments(arguments, &value.place)?;
            }
            vir_mid::Rvalue::Aggregate(value) => {
                for operand in &value.operands {
                    self.encode_operand_arguments(arguments, operand)?;
                }
            }
        }
        Ok(())
    }
    fn encode_operand_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<()> {
        match operand.kind {
            vir_mid::OperandKind::Copy | vir_mid::OperandKind::Move => {
                self.encode_place_arguments(arguments, &operand.expression)?;
            }
            vir_mid::OperandKind::Constant => {
                arguments.push(operand.expression.to_procedure_snapshot(self)?);
            }
        }
        Ok(())
    }
    fn encode_place_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        expression: &vir_mid::Expression,
    ) -> SpannedEncodingResult<()> {
        arguments.push(self.encode_expression_as_place(expression)?);
        arguments.push(self.extract_root_address(expression)?);
        arguments.push(expression.to_procedure_snapshot(self)?);
        Ok(())
    }
    fn encode_lft_tok_sep_take_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("lft_tok_sep_take${}", lft_count))
    }
    fn encode_lft_tok_sep_return_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("lft_tok_sep_return${}", lft_count))
    }
    fn encode_assign_method_name(
        &self,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<String> {
        Ok(format!(
            "assign${}${}",
            ty.get_identifier(),
            value.get_identifier()
        ))
    }
    fn encode_consume_operand_method_name(
        &self,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("consume${}", operand.get_identifier()))
    }
    fn encode_assign_method(
        &mut self,
        method_name: &str,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_assign_methods
            .contains(method_name)
        {
            self.encode_compute_address(ty)?;
            self.encode_write_place_method(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::MovePlace),
            );
            use vir_low::macros::*;
            let compute_address = ty!(Address);
            let size_of = self.encode_type_size_expression(ty)?;
            var_decls! {
                target_place: Place,
                target_address: Address
            };
            let mut parameters = vec![target_place.clone(), target_address.clone()];
            var_decls! { result_value: {ty.to_snapshot(self)?} };
            let mut pres = vec![
                expr! { acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_address)), [size_of])) },
            ];
            let mut posts = Vec::new();
            let mut pre_write_statements = Vec::new();
            let mut post_write_statements = Vec::new();
            match value {
                vir_mid::Rvalue::CheckedBinaryOp(value) => {
                    self.encode_assign_method_rvalue_checked_binary_op(
                        &mut parameters,
                        &mut pres,
                        &mut posts,
                        &mut pre_write_statements,
                        value,
                        ty,
                        &result_value,
                        position,
                    )?;
                }
                vir_mid::Rvalue::Ref(value) => {
                    self.encode_assign_method_rvalue_ref(
                        method_name,
                        parameters,
                        pres,
                        posts,
                        value,
                        ty,
                        result_value,
                        position,
                    )?;
                    return Ok(());
                }
                _ => {
                    post_write_statements.push(stmtp! {
                        position => call write_place<ty>(target_place, target_address, result_value)
                    });
                    posts.push(
                        expr! { acc(OwnedNonAliased<ty>(target_place, target_address, result_value)) },
                    );
                    self.encode_assign_method_rvalue(
                        &mut parameters,
                        &mut pres,
                        &mut posts,
                        &mut pre_write_statements,
                        value,
                        ty,
                        &result_value,
                        position,
                    )?;
                }
            }
            let mut statements = pre_write_statements;
            statements.extend(post_write_statements);
            let method = vir_low::MethodDecl::new(
                method_name,
                parameters,
                vec![result_value],
                pres,
                posts,
                Some(statements),
            );
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_assign_methods
                .insert(method_name.to_string());
        }
        Ok(())
    }
    fn encode_consume_operand_method(
        &mut self,
        method_name: &str,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_consume_operand_methods
            .contains(method_name)
        {
            let mut parameters = Vec::new();
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let mut _pre_write_statements = Vec::new();
            self.encode_assign_operand(
                &mut parameters,
                &mut pres,
                &mut posts,
                &mut _pre_write_statements,
                1,
                operand,
            )?;
            let method =
                vir_low::MethodDecl::new(method_name, parameters, Vec::new(), pres, posts, None);
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_consume_operand_methods
                .insert(method_name.to_string());
        }
        Ok(())
    }
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::Rvalue,
        result_type: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let assigned_value = match value {
            vir_mid::Rvalue::Ref(_value) => {
                unreachable!("Ref should be handled in the caller.");
            }
            vir_mid::Rvalue::AddressOf(value) => {
                let ty = value.place.get_type();
                var_decls! {
                    operand_place: Place,
                    operand_address: Address,
                    operand_value: { ty.to_snapshot(self)? }
                };
                let predicate = expr! {
                    acc(OwnedNonAliased<ty>(operand_place, operand_address, operand_value))
                };
                let compute_address = ty!(Address);
                let address =
                    expr! { ComputeAddress::compute_address(operand_place, operand_address) };
                pres.push(predicate.clone());
                posts.push(predicate);
                parameters.push(operand_place);
                parameters.push(operand_address);
                parameters.push(operand_value);
                self.construct_constant_snapshot(result_type, address, position)?
            }
            vir_mid::Rvalue::UnaryOp(value) => {
                let operand_value = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    pre_write_statements,
                    1,
                    &value.argument,
                )?;
                self.construct_unary_op_snapshot(
                    value.kind,
                    value.argument.expression.get_type(),
                    operand_value.into(),
                    position,
                )?
            }
            vir_mid::Rvalue::BinaryOp(value) => {
                let operand_left = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    pre_write_statements,
                    1,
                    &value.left,
                )?;
                let operand_right = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    pre_write_statements,
                    2,
                    &value.right,
                )?;
                self.construct_binary_op_snapshot(
                    value.kind,
                    value.kind.get_result_type(value.left.expression.get_type()),
                    value.left.expression.get_type(),
                    operand_left.into(),
                    operand_right.into(),
                    position,
                )?
            }
            vir_mid::Rvalue::CheckedBinaryOp(_) => {
                unreachable!("CheckedBinaryOp should be handled in the caller.");
            }
            vir_mid::Rvalue::Discriminant(value) => {
                let ty = value.place.get_type();
                var_decls! {
                    operand_place: Place,
                    operand_address: Address,
                    operand_value: { ty.to_snapshot(self)? }
                };
                let predicate = expr! {
                    acc(OwnedNonAliased<ty>(operand_place, operand_address, operand_value))
                };
                pres.push(predicate.clone());
                posts.push(predicate);
                parameters.push(operand_place);
                parameters.push(operand_address);
                parameters.push(operand_value.clone());
                pres.push(
                    self.encode_snapshot_valid_call_for_type(operand_value.clone().into(), ty)?,
                );
                let discriminant_call =
                    self.obtain_enum_discriminant(operand_value.into(), ty, position)?;
                self.construct_constant_snapshot(result_type, discriminant_call, position)?
            }
            vir_mid::Rvalue::Aggregate(value) => {
                let mut arguments = Vec::new();
                for (i, operand) in value.operands.iter().enumerate() {
                    let operand_value = self.encode_assign_operand(
                        parameters,
                        pres,
                        posts,
                        pre_write_statements,
                        i.try_into().unwrap(),
                        operand,
                    )?;
                    arguments.push(operand_value.into());
                }
                let assigned_value = match &value.ty {
                    vir_mid::Type::Union(_) | vir_mid::Type::Enum(_) => {
                        let variant_constructor =
                            self.construct_struct_snapshot(&value.ty, arguments, position)?;
                        self.construct_enum_snapshot(&value.ty, variant_constructor, position)?
                    }
                    vir_mid::Type::Struct(_) | vir_mid::Type::Tuple(_) => {
                        self.construct_struct_snapshot(&value.ty, arguments, position)?
                    }
                    ty => unimplemented!("{}", ty),
                };
                posts.push(
                    self.encode_snapshot_valid_call_for_type(assigned_value.clone(), result_type)?,
                );
                assigned_value
            }
        };
        posts.push(exprp! { position => result_value == [assigned_value.clone()]});
        pre_write_statements.push(vir_low::Statement::assign(
            result_value.clone(),
            assigned_value,
            position,
        ));
        Ok(())
    }
    fn encode_assign_method_rvalue_checked_binary_op(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::ast::rvalue::CheckedBinaryOp,
        ty: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        // In case the operation fails, the state of the assigned value
        // is unknown.
        use vir_low::macros::*;
        var_decls! {
            target_place: Place,
            target_address: Address
        };
        let compute_address = ty!(Address);
        let type_decl = self.encoder.get_type_decl_mid(ty)?.unwrap_tuple();
        let (operation_result_field, flag_field) = {
            let mut iter = type_decl.iter_fields();
            (iter.next().unwrap(), iter.next().unwrap())
        };
        let flag_place =
            self.encode_field_place(ty, &flag_field, target_place.clone().into(), position)?;
        let flag_value = self.obtain_struct_field_snapshot(
            ty,
            &flag_field,
            result_value.clone().into(),
            position,
        )?;
        let result_address =
            expr! { (ComputeAddress::compute_address(target_place, target_address)) };
        let operation_result_address = self.encode_field_address(
            ty,
            &operation_result_field,
            result_address.clone(),
            position,
        )?;
        let operation_result_value = self.obtain_struct_field_snapshot(
            ty,
            &operation_result_field,
            result_value.clone().into(),
            position,
        )?;
        let flag_type = &vir_mid::Type::Bool;
        let operation_result_type = value.kind.get_result_type(value.left.expression.get_type());
        let size_of_result = self.encode_type_size_expression(operation_result_type)?;
        let post_write_statements = vec![
            stmtp! { position =>
                call memory_block_split<ty>([result_address])
            },
            stmtp! { position =>
                call write_address<operation_result_type>([operation_result_address.clone()], [operation_result_value.clone()])
            },
            stmtp! { position =>
                call write_place<flag_type>([flag_place.clone()], target_address, [flag_value.clone()])
            },
        ];
        posts.push(
            expr! { acc(MemoryBlock([operation_result_address.clone()], [size_of_result.clone()])) },
        );
        posts.push(
            expr! { acc(OwnedNonAliased<flag_type>([flag_place], target_address, [flag_value.clone()])) },
        );
        let operand_left = self.encode_assign_operand(
            parameters,
            pres,
            posts,
            pre_write_statements,
            1,
            &value.left,
        )?;
        let operand_right = self.encode_assign_operand(
            parameters,
            pres,
            posts,
            pre_write_statements,
            2,
            &value.right,
        )?;
        let operation_result = self.construct_binary_op_snapshot(
            value.kind,
            operation_result_type,
            value.left.expression.get_type(),
            operand_left.into(),
            operand_right.into(),
            position,
        )?;
        let validity = self
            .encode_snapshot_valid_call_for_type(operation_result.clone(), operation_result_type)?;
        let flag_result = self.construct_constant_snapshot(
            &vir_mid::Type::Bool,
            vir_low::Expression::not(validity.clone()),
            position,
        )?;
        pre_write_statements.push(vir_low::Statement::comment(
            "Viper does not support ADT assignments, so we use an assume.".to_string(),
        ));
        let operation_result_value_condition = expr! {
            [validity] ==> ([operation_result_value.clone()] == [operation_result])
        };
        pre_write_statements.push(stmtp! { position =>
            assume ([operation_result_value_condition.clone()])
        });
        let flag_value_condition = expr! {
            [flag_value] == [flag_result]
        };
        pre_write_statements.push(stmtp! { position =>
            assume ([flag_value_condition.clone()])
        });
        pre_write_statements.extend(post_write_statements);
        posts.push(operation_result_value_condition);
        posts.push(flag_value_condition);
        let bytes =
            self.encode_memory_block_bytes_expression(operation_result_address, size_of_result)?;
        let to_bytes = ty! { Bytes };
        posts.push(expr! {
            [bytes] == (Snap<operation_result_type>::to_bytes([operation_result_value]))
        });
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue_ref(
        &mut self,
        method_name: &str,
        mut parameters: Vec<vir_low::VariableDecl>,
        mut pres: Vec<vir_low::Expression>,
        mut posts: Vec<vir_low::Expression>,
        value: &vir_mid::ast::rvalue::Ref,
        result_type: &vir_mid::Type,
        result_value: vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let ty = value.place.get_type();
        var_decls! {
            target_place: Place,
            target_address: Address,
            operand_place: Place,
            operand_address: Address,
            operand_value: { ty.to_snapshot(self)? },
            operand_lifetime: Lifetime,
            lifetime_perm: Perm
        };
        let predicate = expr! {
            acc(OwnedNonAliased<ty>(operand_place, operand_address, operand_value))
        };
        let reference_predicate = expr! {
            acc(OwnedNonAliased<result_type>(target_place, target_address, result_value, operand_lifetime))
        };
        let lifetime_token =
            self.encode_lifetime_token(operand_lifetime.clone(), lifetime_perm.clone().into())?;
        let final_snapshot = self.reference_target_final_snapshot(
            result_type,
            result_value.clone().into(),
            position,
        )?;
        let validity = self.encode_snapshot_valid_call_for_type(final_snapshot.clone(), ty)?;
        let restoration = expr! {
            wand(
                (acc(DeadLifetimeToken(operand_lifetime))) --* (
                    (acc(OwnedNonAliased<ty>(operand_place, operand_address, [final_snapshot]))) &&
                    [validity] &&
                    // DeadLifetimeToken is duplicable and does not get consumed.
                    (acc(DeadLifetimeToken(operand_lifetime)))
                )
            )
        };
        let compute_address = ty!(Address);
        let _address = expr! { ComputeAddress::compute_address(operand_place, operand_address) };
        pres.push(expr! {
            [vir_low::Expression::no_permission()] < lifetime_perm
        });
        pres.push(expr! {
            lifetime_perm < [vir_low::Expression::full_permission()]
        });
        pres.push(predicate);
        pres.push(lifetime_token.clone());
        posts.push(lifetime_token);
        posts.push(reference_predicate);
        posts.push(restoration);
        parameters.push(operand_place);
        parameters.push(operand_address);
        parameters.push(operand_value);
        parameters.push(operand_lifetime);
        parameters.push(lifetime_perm);
        let method = vir_low::MethodDecl::new(
            method_name,
            parameters,
            vec![result_value],
            pres,
            posts,
            None,
        );
        self.declare_method(method)?;
        self.builtin_methods_state
            .encoded_assign_methods
            .insert(method_name.to_string());
        Ok(())
    }
    fn encode_assign_operand(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        use vir_low::macros::*;
        let value = self.encode_assign_operand_snapshot(operand_counter, operand)?;
        let ty = operand.expression.get_type();
        match operand.kind {
            vir_mid::OperandKind::Copy | vir_mid::OperandKind::Move => {
                let place = self.encode_assign_operand_place(operand_counter)?;
                let root_address = self.encode_assign_operand_address(operand_counter)?;
                pres.push(expr! { acc(OwnedNonAliased<ty>(place, root_address, value)) });
                let post_predicate = if operand.kind == vir_mid::OperandKind::Copy {
                    expr! { acc(OwnedNonAliased<ty>(place, root_address, value)) }
                } else {
                    self.encode_into_memory_block_method(ty)?;
                    pre_write_statements
                        .push(stmt! { call into_memory_block<ty>(place, root_address, value) });
                    let compute_address = ty!(Address);
                    let size_of = self.encode_type_size_expression(ty)?;
                    expr! { acc(MemoryBlock((ComputeAddress::compute_address(place, root_address)), [size_of])) }
                };
                posts.push(post_predicate);
                parameters.push(place);
                parameters.push(root_address);
            }
            vir_mid::OperandKind::Constant => {}
        }
        pres.push(self.encode_snapshot_valid_call_for_type(value.clone().into(), ty)?);
        parameters.push(value.clone());
        Ok(value)
    }
    fn encode_assign_operand_place(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{}_place", operand_counter),
            self.place_type()?,
        ))
    }
    fn encode_assign_operand_address(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{}_root_address", operand_counter),
            self.address_type()?,
        ))
    }
    fn encode_assign_operand_snapshot(
        &mut self,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{}_value", operand_counter),
            operand.expression.get_type().to_snapshot(self)?,
        ))
    }
}

pub(in super::super) trait BuiltinMethodsInterface {
    fn encode_write_address_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_move_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_copy_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_write_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_memory_block_split_method(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_into_memory_block_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_assign_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: vir_mid::Expression,
        value: vir_mid::Rvalue,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_consume_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        operand: vir_mid::Operand,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_tok_sep_take_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()>;
    fn encode_lft_tok_sep_return_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()>;
    fn encode_newlft_method(&mut self) -> SpannedEncodingResult<()>;
    fn encode_endlft_method(&mut self) -> SpannedEncodingResult<()>;
    fn encode_open_close_mut_ref_methods(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> BuiltinMethodsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_write_address_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_write_address_methods
            .contains(ty)
        {
            self.encode_snapshot_to_bytes_function(ty)?;
            self.encode_memory_block_predicate()?;
            use vir_low::macros::*;
            let size_of = self.encode_type_size_expression(ty)?;
            let to_bytes = ty! { Bytes };
            let method = method! {
                write_address<ty>(
                    address: Address,
                    value: {ty.to_snapshot(self)?}
                ) returns ()
                    raw_code {
                        let bytes = self.encode_memory_block_bytes_expression(
                            address.clone().into(),
                            size_of.clone(),
                        )?;
                    }
                    requires (acc(MemoryBlock((address), [size_of.clone()])));
                    ensures (acc(MemoryBlock((address), [size_of])));
                    ensures (([bytes]) == (Snap<ty>::to_bytes(value)));
            };
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_write_address_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    fn encode_move_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        // TODO: Remove code duplication with encode_copy_place_method and encode_write_place_method
        if !self
            .builtin_methods_state
            .encoded_move_place_methods
            .contains(ty)
        {
            self.encode_compute_address(ty)?;
            self.encode_write_place_method(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::MovePlace),
            );
            use vir_low::macros::*;
            let size_of = self.encode_type_size_expression(ty)?;
            let compute_address = ty!(Address);
            let to_bytes = ty! { Bytes };
            let mut statements = Vec::new();
            var_decls! {
                    target_place: Place,
                    target_root_address: Address,
                    source_place: Place,
                    source_root_address: Address,
                    source_value: {ty.to_snapshot(self)?}
            };
            let source_address =
                expr! { ComputeAddress::compute_address(source_place, source_root_address) };
            let bytes =
                self.encode_memory_block_bytes_expression(source_address.clone(), size_of.clone())?;
            let target_address =
                expr! { ComputeAddress::compute_address(target_place, target_root_address) };
            statements.push(stmtp! { position =>
                unfold OwnedNonAliased<ty>(source_place, source_root_address, source_value)
            });
            self.mark_owned_non_aliased_as_unfolded(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            match type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_) => {
                    self.encode_write_address_method(ty)?;
                    statements.push(stmtp! { position =>
                        // TODO: Replace with memcopy.
                        call write_address<ty>([target_address], source_value)
                    });
                }
                vir_mid::TypeDecl::TypeVar(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Tuple(decl) => {
                    if decl.arguments.is_empty() {
                        self.encode_write_address_method(ty)?;
                        statements.push(stmtp! { position =>
                            // TODO: Replace with memcopy.
                            call write_address<ty>([target_address], source_value)
                        });
                    } else {
                        unimplemented!()
                    }
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    if decl.fields.is_empty() {
                        self.encode_write_address_method(ty)?;
                        statements.push(stmtp! { position =>
                            // TODO: Replace with memcopy.
                            call write_address<ty>([target_address], source_value)
                        });
                    } else {
                        self.encode_memory_block_split_method(ty)?;
                        statements.push(stmtp! {
                            position =>
                            call memory_block_split<ty>([target_address])
                        });
                        for field in &decl.fields {
                            let source_field_place = self.encode_field_place(
                                ty,
                                field,
                                source_place.clone().into(),
                                position,
                            )?;
                            let target_field_place = self.encode_field_place(
                                ty,
                                field,
                                target_place.clone().into(),
                                position,
                            )?;
                            let source_field_value = self.obtain_struct_field_snapshot(
                                ty,
                                field,
                                source_value.clone().into(),
                                position,
                            )?;
                            let field_type = &field.ty;
                            self.encode_move_place_method(field_type)?;
                            statements.push(stmtp! { position =>
                                call move_place<field_type>(
                                    [target_field_place],
                                    target_root_address,
                                    [source_field_place],
                                    source_root_address,
                                    [source_field_value]
                                )
                            });
                        }
                        self.encode_memory_block_join_method(ty)?;
                        statements.push(stmtp! {
                            position =>
                            call memory_block_join<ty>([source_address])
                        });
                    }
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    let discriminant_call =
                        self.obtain_enum_discriminant(source_value.clone().into(), ty, position)?;
                    self.encode_memory_block_split_method(ty)?;
                    statements.push(stmtp! {
                        position =>
                        call memory_block_split<ty>([target_address], [discriminant_call.clone()])
                    });
                    for (&discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.into()]
                        };
                        let source_variant_place = self.encode_enum_variant_place(
                            ty,
                            &variant_index,
                            source_place.clone().into(),
                            position,
                        )?;
                        let target_variant_place = self.encode_enum_variant_place(
                            ty,
                            &variant_index,
                            target_place.clone().into(),
                            position,
                        )?;
                        let source_variant_value = self.obtain_enum_variant_snapshot(
                            ty,
                            &variant_index,
                            source_value.clone().into(),
                            position,
                        )?;
                        let variant_ty = &ty.clone().variant(variant_index);
                        self.encode_move_place_method(variant_ty)?;
                        statements.push(stmtp! { position =>
                            call<condition> move_place<variant_ty>(
                                [target_variant_place],
                                target_root_address,
                                [source_variant_place],
                                source_root_address,
                                [source_variant_value]
                            )
                        });
                    }
                    let discriminant_field = decl.discriminant_field();
                    let target_discriminant_place = self.encode_field_place(
                        ty,
                        &discriminant_field,
                        target_place.clone().into(),
                        position,
                    )?;
                    let source_discriminant_place = self.encode_field_place(
                        ty,
                        &discriminant_field,
                        source_place.clone().into(),
                        position,
                    )?;
                    let discriminant_type = &decl.discriminant_type;
                    let source_discriminant_value = self.construct_constant_snapshot(
                        discriminant_type,
                        discriminant_call.clone(),
                        position,
                    )?;
                    self.encode_move_place_method(discriminant_type)?;
                    statements.push(stmtp! { position =>
                        call move_place<discriminant_type>(
                            [target_discriminant_place],
                            target_root_address,
                            [source_discriminant_place],
                            source_root_address,
                            [source_discriminant_value]
                        )
                    });
                    self.encode_memory_block_join_method(ty)?;
                    statements.push(stmtp! {
                        position =>
                        call memory_block_join<ty>([source_address], [discriminant_call])
                    });
                }
                vir_mid::TypeDecl::Union(_decl) => {
                    unimplemented!();
                }
                vir_mid::TypeDecl::Array(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Sequence(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Map(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Reference(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Never => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Closure(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Unsupported(_) => {
                    unimplemented!()
                }
            }
            statements.push(stmtp! { position =>
                fold OwnedNonAliased<ty>(target_place, target_root_address, source_value)
            });
            let method = vir_low::MethodDecl::new(
                method_name! { move_place<ty> },
                vec![
                    target_place.clone(),
                    target_root_address.clone(),
                    source_place.clone(),
                    source_root_address.clone(),
                    source_value.clone(),
                ],
                Vec::new(),
                vec![
                    expr! {(acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_root_address)), [size_of.clone()])))},
                    expr! {(acc(OwnedNonAliased<ty>(source_place, source_root_address, source_value)))},
                ],
                vec![
                    expr! {(acc(OwnedNonAliased<ty>(target_place, target_root_address, source_value)))},
                    expr! {(acc(MemoryBlock((ComputeAddress::compute_address(source_place, source_root_address)), [size_of])))},
                    expr! {(([bytes]) == (Snap<ty>::to_bytes(source_value)))},
                ],
                Some(statements),
            );
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_move_place_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    fn encode_copy_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        // TODO: Remove code duplication with encode_move_place_method
        if !self
            .builtin_methods_state
            .encoded_copy_place_methods
            .contains(ty)
        {
            self.encode_compute_address(ty)?;
            self.encode_write_place_method(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::MovePlace),
            );
            use vir_low::macros::*;
            let size_of = self.encode_type_size_expression(ty)?;
            let compute_address = ty!(Address);
            let mut statements = Vec::new();
            let mut method = method! {
                copy_place<ty>(
                    target_place: Place,
                    target_address: Address,
                    source_place: Place,
                    source_address: Address,
                    source_value: {ty.to_snapshot(self)?}
                ) returns ()
                    raw_code {
                        self.encode_fully_unfold_owned_non_aliased(
                            &mut statements,
                            ty,
                            source_place.clone().into(),
                            &Into::<vir_low::Expression>::into(source_address.clone()),
                            source_value.clone().into(),
                            position,
                        )?;
                        let address = expr! { ComputeAddress::compute_address(source_place, source_address) };
                        self.encode_fully_join_memory_block(
                            &mut statements,
                            ty,
                            address.clone(),
                            position,
                        )?;
                        statements.push(stmtp! { position =>
                            call write_place<ty>(target_place, target_address, source_value)
                        });
                        let to_bytes = ty! { Bytes };
                        let memory_block_bytes =
                            self.encode_memory_block_bytes_expression(address, size_of.clone())?;
                        statements.push(stmtp! { position =>
                            assert ([memory_block_bytes] == (Snap<ty>::to_bytes(source_value)))
                        });
                        self.encode_fully_split_memory_block(
                            &mut statements,
                            ty,
                            expr! { ComputeAddress::compute_address(source_place, source_address) },
                            position,
                        )?;
                        self.encode_fully_fold_owned_non_aliased(
                            &mut statements,
                            ty,
                            source_place.clone().into(),
                            &Into::<vir_low::Expression>::into(source_address.clone()),
                            source_value.clone().into(),
                            position,
                        )?;
                    }
                    requires (acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_address)), [size_of])));
                    requires (acc(OwnedNonAliased<ty>(source_place, source_address, source_value)));
                    ensures (acc(OwnedNonAliased<ty>(target_place, target_address, source_value)));
                    ensures (acc(OwnedNonAliased<ty>(source_place, source_address, source_value)));
            };
            method.body = Some(statements);
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_copy_place_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    fn encode_write_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        // TODO: Remove code duplication with encode_copy_place_method and encode_write_place_method
        if !self
            .builtin_methods_state
            .encoded_write_place_methods
            .contains(ty)
        {
            self.encode_compute_address(ty)?;
            self.encode_write_address_method(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::WritePlace),
            );
            use vir_low::macros::*;
            let compute_address = ty!(Address);
            let size_of = self.encode_type_size_expression(ty)?;
            let mut statements = Vec::new();
            var_decls! {
                place: Place,
                root_address: Address,
                value: {ty.to_snapshot(self)?}
            };
            let validity = self.encode_snapshot_valid_call_for_type(value.clone().into(), ty)?;
            let address = expr! { ComputeAddress::compute_address(place, root_address) };
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            self.mark_owned_non_aliased_as_unfolded(ty)?;
            match type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_) => {
                    self.encode_write_address_method(ty)?;
                    statements.push(stmtp! { position =>
                        call write_address<ty>([address.clone()], value)
                    });
                }
                vir_mid::TypeDecl::TypeVar(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Tuple(decl) => {
                    if decl.arguments.is_empty() {
                        self.encode_write_address_method(ty)?;
                        statements.push(stmtp! { position =>
                            call write_address<ty>([address.clone()], value)
                        });
                    } else {
                        self.encode_memory_block_split_method(ty)?;
                        statements.push(stmtp! {
                            position =>
                            call memory_block_split<ty>([address.clone()])
                        });
                        for field in decl.iter_fields() {
                            let field_place = self.encode_field_place(
                                ty,
                                &field,
                                place.clone().into(),
                                position,
                            )?;
                            let field_value = self.obtain_struct_field_snapshot(
                                ty,
                                &field,
                                value.clone().into(),
                                position,
                            )?;
                            let field_type = &field.ty;
                            self.encode_write_place_method(field_type)?;
                            statements.push(stmtp! { position =>
                                call write_place<field_type>(
                                    [field_place], root_address, [field_value]
                                )
                            });
                        }
                    }
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    if decl.fields.is_empty() {
                        self.encode_write_address_method(ty)?;
                        statements.push(stmtp! { position =>
                            call write_address<ty>([address.clone()], value)
                        });
                    } else {
                        self.encode_memory_block_split_method(ty)?;
                        statements.push(stmtp! {
                            position =>
                            call memory_block_split<ty>([address.clone()])
                        });
                        for field in &decl.fields {
                            let field_place =
                                self.encode_field_place(ty, field, place.clone().into(), position)?;
                            let field_value = self.obtain_struct_field_snapshot(
                                ty,
                                field,
                                value.clone().into(),
                                position,
                            )?;
                            let field_type = &field.ty;
                            self.encode_write_place_method(field_type)?;
                            statements.push(stmtp! { position =>
                                call write_place<field_type>(
                                    [field_place], root_address, [field_value]
                                )
                            });
                        }
                    }
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    let discriminant_call =
                        self.obtain_enum_discriminant(value.clone().into(), ty, position)?;
                    self.encode_memory_block_split_method(ty)?;
                    statements.push(stmtp! {
                        position =>
                        call memory_block_split<ty>([address.clone()], [discriminant_call.clone()])
                    });
                    for (&discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.into()]
                        };
                        let variant_place = self.encode_enum_variant_place(
                            ty,
                            &variant_index,
                            place.clone().into(),
                            position,
                        )?;
                        let variant_value = self.obtain_enum_variant_snapshot(
                            ty,
                            &variant_index,
                            value.clone().into(),
                            position,
                        )?;
                        let variant_ty = &ty.clone().variant(variant_index);
                        self.encode_write_place_method(variant_ty)?;
                        statements.push(stmtp! { position =>
                            call<condition> write_place<variant_ty>(
                                [variant_place], root_address, [variant_value]
                            )
                        });
                    }
                    let discriminant_field = decl.discriminant_field();
                    let discriminant_place = self.encode_field_place(
                        ty,
                        &discriminant_field,
                        place.clone().into(),
                        position,
                    )?;
                    let discriminant_type = &decl.discriminant_type;
                    let discriminant_value = self.construct_constant_snapshot(
                        discriminant_type,
                        discriminant_call,
                        position,
                    )?;
                    self.encode_write_place_method(discriminant_type)?;
                    statements.push(stmtp! { position =>
                        call write_place<discriminant_type>(
                            [discriminant_place], root_address, [discriminant_value]
                        )
                    });
                }
                vir_mid::TypeDecl::Union(decl) => {
                    let discriminant_call =
                        self.obtain_enum_discriminant(value.clone().into(), ty, position)?;
                    self.encode_memory_block_split_method(ty)?;
                    statements.push(stmtp! {
                        position =>
                        call memory_block_split<ty>([address.clone()], [discriminant_call.clone()])
                    });
                    for (&discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.into()]
                        };
                        let variant_place = self.encode_enum_variant_place(
                            ty,
                            &variant_index,
                            place.clone().into(),
                            position,
                        )?;
                        let variant_value = self.obtain_enum_variant_snapshot(
                            ty,
                            &variant_index,
                            value.clone().into(),
                            position,
                        )?;
                        let variant_ty = &ty.clone().variant(variant_index);
                        self.encode_write_place_method(variant_ty)?;
                        statements.push(stmtp! { position =>
                            call<condition> write_place<variant_ty>(
                                [variant_place], root_address, [variant_value]
                            )
                        });
                    }
                }
                vir_mid::TypeDecl::Array(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Map(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Reference(_) => {
                    // References should never be written through `write_place`.
                    return Ok(());
                }
                vir_mid::TypeDecl::Never => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Closure(_) => {
                    unimplemented!()
                }
                vir_mid::TypeDecl::Unsupported(_) => {
                    unimplemented!()
                }
            }
            statements.push(stmtp! { position =>
                fold OwnedNonAliased<ty>(place, root_address, value)
            });
            let method = vir_low::MethodDecl::new(
                method_name! { write_place<ty> },
                vec![place.clone(), root_address.clone(), value.clone()],
                Vec::new(),
                vec![expr! { (acc(MemoryBlock([address], [size_of]))) }, validity],
                vec![expr! { (acc(OwnedNonAliased<ty>(place, root_address, value))) }],
                Some(statements),
            );
            self.declare_method(method.set_default_position(position))?;
            self.builtin_methods_state
                .encoded_write_place_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    fn encode_memory_block_split_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_memory_block_split_methods
            .contains(ty)
        {
            use vir_low::macros::*;
            let method = if ty.has_variants() {
                // TODO: remove code duplication with encode_memory_block_join_method
                let type_decl = self.encoder.get_type_decl_mid(ty)?;
                match type_decl {
                    vir_mid::TypeDecl::Enum(enum_decl) => {
                        var_decls!(address: Address, discriminant: Int);
                        let size_of = self.encode_type_size_expression(ty)?;
                        let whole_block = expr!(acc(MemoryBlock(address, [size_of])));
                        let discriminant_field = enum_decl.discriminant_field();
                        let discriminant_size_of =
                            self.encode_type_size_expression(&enum_decl.discriminant_type)?;
                        let discriminant_address = self.encode_field_address(
                            ty,
                            &discriminant_field,
                            address.clone().into(),
                            Default::default(),
                        )?;
                        let mut postconditions = vec![
                            expr! { acc(MemoryBlock([discriminant_address], [discriminant_size_of]))},
                        ];
                        for (&discriminant_value, variant) in enum_decl
                            .discriminant_values
                            .iter()
                            .zip(&enum_decl.variants)
                        {
                            let variant_index = variant.name.clone().into();
                            let variant_address = self.encode_enum_variant_address(
                                ty,
                                &variant_index,
                                address.clone().into(),
                                Default::default(),
                            )?;
                            let variant_type = ty.clone().variant(variant_index);
                            let variant_size_of =
                                self.encode_type_size_expression(&variant_type)?;
                            postconditions.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (acc(MemoryBlock([variant_address], [variant_size_of])))
                            })
                        }
                        vir_low::MethodDecl::new(
                            method_name! { memory_block_split<ty> },
                            vec![address, discriminant],
                            Vec::new(),
                            vec![whole_block],
                            postconditions,
                            None,
                        )
                    }
                    vir_mid::TypeDecl::Union(enum_decl) => {
                        var_decls!(address: Address, discriminant: Int);
                        let size_of = self.encode_type_size_expression(ty)?;
                        let whole_block = expr!(acc(MemoryBlock(address, [size_of])));
                        let mut postconditions = Vec::new();
                        for (&discriminant_value, variant) in enum_decl
                            .discriminant_values
                            .iter()
                            .zip(&enum_decl.variants)
                        {
                            let variant_index = variant.name.clone().into();
                            let variant_address = self.encode_enum_variant_address(
                                ty,
                                &variant_index,
                                address.clone().into(),
                                Default::default(),
                            )?;
                            let variant_type = ty.clone().variant(variant_index);
                            let variant_size_of =
                                self.encode_type_size_expression(&variant_type)?;
                            postconditions.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (acc(MemoryBlock([variant_address], [variant_size_of])))
                            })
                        }
                        vir_low::MethodDecl::new(
                            method_name! { memory_block_split<ty> },
                            vec![address, discriminant],
                            Vec::new(),
                            vec![whole_block],
                            postconditions,
                            None,
                        )
                    }
                    _ => {
                        unreachable!("only enums and unions has variants")
                    }
                }
            } else {
                let mut helper = SplitJoinHelper::new(false);
                helper.walk_type(ty, (), self)?;
                let to_bytes = ty! { Bytes };
                var_decls! { address: Address };
                let size_of = self.encode_type_size_expression(ty)?;
                let memory_block_bytes =
                    self.encode_memory_block_bytes_expression(address.into(), size_of)?;
                let bytes_quantifier = expr! {
                    forall(
                        snapshot: {ty.to_snapshot(self)?} ::
                        [ { (Snap<ty>::to_bytes(snapshot)) } ]
                        ((old([memory_block_bytes])) == (Snap<ty>::to_bytes(snapshot))) ==>
                        [ helper.field_to_bytes_equalities.into_iter().conjoin() ]
                    )
                };
                helper.postconditions.push(bytes_quantifier);
                vir_low::MethodDecl::new(
                    method_name! { memory_block_split<ty> },
                    vars! { address: Address },
                    Vec::new(),
                    helper.preconditions,
                    helper.postconditions,
                    None,
                )
            };
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_memory_block_split_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_memory_block_join_methods
            .contains(ty)
        {
            use vir_low::macros::*;
            self.encode_snapshot_to_bytes_function(ty)?;
            let method = if ty.has_variants() {
                // TODO: remove code duplication with encode_memory_block_split_method
                let type_decl = self.encoder.get_type_decl_mid(ty)?;
                match type_decl {
                    vir_mid::TypeDecl::Enum(enum_decl) => {
                        var_decls!(address: Address, discriminant: Int);
                        let size_of = self.encode_type_size_expression(ty)?;
                        let whole_block = expr!(acc(MemoryBlock(address, [size_of.clone()])));
                        let discriminant_field = enum_decl.discriminant_field();
                        let discriminant_size_of =
                            self.encode_type_size_expression(&enum_decl.discriminant_type)?;
                        let discriminant_address = self.encode_field_address(
                            ty,
                            &discriminant_field,
                            address.clone().into(),
                            Default::default(),
                        )?;
                        let discriminant_expr: vir_low::Expression = discriminant.clone().into();
                        let discriminant_bounds = discriminant_expr
                            .generate_discriminant_bounds(&enum_decl.discriminant_bounds);
                        let mut preconditions = vec![
                            expr! { acc(MemoryBlock([discriminant_address.clone()], [discriminant_size_of.clone()]))},
                            discriminant_bounds,
                        ];
                        let to_bytes = ty! { Bytes };
                        let mut bytes_quantifier_conjuncts = Vec::new();
                        let memory_block_bytes = self.encode_memory_block_bytes_expression(
                            address.clone().into(),
                            size_of,
                        )?;
                        let snapshot: vir_low::Expression =
                            var! { snapshot: {ty.to_snapshot(self)?} }.into();
                        for (&discriminant_value, variant) in enum_decl
                            .discriminant_values
                            .iter()
                            .zip(&enum_decl.variants)
                        {
                            let variant_index = variant.name.clone().into();
                            let variant_address = self.encode_enum_variant_address(
                                ty,
                                &variant_index,
                                address.clone().into(),
                                Default::default(),
                            )?;

                            let variant_snapshot = self.obtain_enum_variant_snapshot(
                                ty,
                                &variant_index,
                                snapshot.clone(),
                                Default::default(),
                            )?;
                            let variant_type = &ty.clone().variant(variant_index);
                            let variant_size_of = self.encode_type_size_expression(variant_type)?;
                            preconditions.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (acc(MemoryBlock([variant_address.clone()], [variant_size_of.clone()])))
                            });
                            let memory_block_field_bytes = self
                                .encode_memory_block_bytes_expression(
                                    discriminant_address.clone(),
                                    discriminant_size_of.clone(),
                                )?;
                            let discriminant_type = &enum_decl.discriminant_type;
                            let discriminant_call = self.obtain_enum_discriminant(
                                snapshot.clone(),
                                ty,
                                Default::default(),
                            )?;
                            let discriminant_snapshot = self.construct_constant_snapshot(
                                discriminant_type,
                                discriminant_call,
                                Default::default(),
                            )?;
                            let memory_block_variant_bytes = self
                                .encode_memory_block_bytes_expression(
                                    variant_address,
                                    variant_size_of,
                                )?;
                            bytes_quantifier_conjuncts.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (
                                    (
                                        ((old([memory_block_field_bytes])) == (Snap<discriminant_type>::to_bytes([discriminant_snapshot]))) &&
                                        ((old([memory_block_variant_bytes])) == (Snap<variant_type>::to_bytes([variant_snapshot])))
                                    ) ==>
                                    ([memory_block_bytes.clone()] == (Snap<ty>::to_bytes([snapshot.clone()])))
                                )
                            });
                        }
                        let bytes_quantifier = expr! {
                            forall(
                                snapshot: {ty.to_snapshot(self)?} ::
                                [ { (Snap<ty>::to_bytes(snapshot)) } ]
                                [ bytes_quantifier_conjuncts.into_iter().conjoin() ]
                            )
                        };
                        vir_low::MethodDecl::new(
                            method_name! { memory_block_join<ty> },
                            vec![address, discriminant],
                            Vec::new(),
                            preconditions,
                            vec![whole_block, bytes_quantifier],
                            None,
                        )
                    }
                    vir_mid::TypeDecl::Union(enum_decl) => {
                        var_decls!(address: Address, discriminant: Int);
                        let size_of = self.encode_type_size_expression(ty)?;
                        let whole_block = expr!(acc(MemoryBlock(address, [size_of.clone()])));
                        let discriminant_expr: vir_low::Expression = discriminant.clone().into();
                        let discriminant_bounds = discriminant_expr
                            .generate_discriminant_bounds(&enum_decl.discriminant_bounds);
                        let mut preconditions = vec![discriminant_bounds];
                        let to_bytes = ty! { Bytes };
                        let mut bytes_quantifier_conjuncts = Vec::new();
                        let memory_block_bytes = self.encode_memory_block_bytes_expression(
                            address.clone().into(),
                            size_of,
                        )?;
                        let snapshot: vir_low::Expression =
                            var! { snapshot: {ty.to_snapshot(self)?} }.into();
                        for (&discriminant_value, variant) in enum_decl
                            .discriminant_values
                            .iter()
                            .zip(&enum_decl.variants)
                        {
                            let variant_index = variant.name.clone().into();
                            let variant_address = self.encode_enum_variant_address(
                                ty,
                                &variant_index,
                                address.clone().into(),
                                Default::default(),
                            )?;

                            let variant_snapshot = self.obtain_enum_variant_snapshot(
                                ty,
                                &variant_index,
                                snapshot.clone(),
                                Default::default(),
                            )?;
                            let variant_type = &ty.clone().variant(variant_index);
                            let variant_size_of = self.encode_type_size_expression(variant_type)?;
                            preconditions.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (acc(MemoryBlock([variant_address.clone()], [variant_size_of.clone()])))
                            });
                            let memory_block_variant_bytes = self
                                .encode_memory_block_bytes_expression(
                                    variant_address,
                                    variant_size_of,
                                )?;
                            bytes_quantifier_conjuncts.push(expr! {
                                (discriminant == [discriminant_value.into()]) ==>
                                (
                                    (
                                        ((old([memory_block_variant_bytes])) == (Snap<variant_type>::to_bytes([variant_snapshot])))
                                    ) ==>
                                    ([memory_block_bytes.clone()] == (Snap<ty>::to_bytes([snapshot.clone()])))
                                )
                            });
                        }
                        let bytes_quantifier = expr! {
                            forall(
                                snapshot: {ty.to_snapshot(self)?} ::
                                [ { (Snap<ty>::to_bytes(snapshot)) } ]
                                [ bytes_quantifier_conjuncts.into_iter().conjoin() ]
                            )
                        };
                        vir_low::MethodDecl::new(
                            method_name! { memory_block_join<ty> },
                            vec![address, discriminant],
                            Vec::new(),
                            preconditions,
                            vec![whole_block, bytes_quantifier],
                            None,
                        )
                    }
                    _ => {
                        unreachable!("only enums and unions has variants")
                    }
                }
            } else {
                let mut helper = SplitJoinHelper::new(true);
                helper.walk_type(ty, (), self)?;
                let to_bytes = ty! { Bytes };
                var_decls! { address: Address };
                let size_of = self.encode_type_size_expression(ty)?;
                let memory_block_bytes =
                    self.encode_memory_block_bytes_expression(address.into(), size_of)?;
                let bytes_quantifier = expr! {
                    forall(
                        snapshot: {ty.to_snapshot(self)?} ::
                        [ { (Snap<ty>::to_bytes(snapshot)) } ]
                        [ helper.field_to_bytes_equalities.into_iter().conjoin() ] ==>
                        ([memory_block_bytes] == (Snap<ty>::to_bytes(snapshot)))
                    )
                };
                helper.postconditions.push(bytes_quantifier);
                vir_low::MethodDecl::new(
                    method_name! { memory_block_join<ty> },
                    vars! { address: Address },
                    Vec::new(),
                    helper.preconditions,
                    helper.postconditions,
                    None,
                )
            };
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_memory_block_join_methods
                .insert(ty.clone());
        }
        Ok(())
    }
    // FIXME: This method has to be inlined if the converted type has a resource
    // invariant in it. Otherwise, that resource would be leaked.
    fn encode_into_memory_block_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_into_memory_block_methods
            .contains(ty)
        {
            self.builtin_methods_state
                .encoded_into_memory_block_methods
                .insert(ty.clone());
            use vir_low::macros::*;
            self.mark_owned_non_aliased_as_unfolded(ty)?;
            let size_of = self.encode_type_size_expression(ty)?;
            let compute_address = ty!(Address);
            let to_bytes = ty! { Bytes };
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::IntoMemoryBlock),
            );
            let mut statements = Vec::new();
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let lifetimes = self.extract_lifetime_variables_from_definition(&type_decl)?;
            let lifetimes_copy = lifetimes.clone();
            let lifetime_exprs = lifetimes.iter().cloned().map(|lifetime| lifetime.into());
            let mut method = method! {
                into_memory_block<ty>(
                    place: Place,
                    root_address: Address,
                    value: {ty.to_snapshot(self)?},
                    *lifetimes
                ) returns ()
                    raw_code {
                        let address = expr! {
                            ComputeAddress::compute_address(place, root_address)
                        };
                        let bytes = self.encode_memory_block_bytes_expression(
                            address.clone(), size_of.clone()
                        )?;
                        statements.push(stmtp! {
                            position =>
                            unfold OwnedNonAliased<ty>(place, root_address, value; lifetime_exprs)
                        });
                        match type_decl {
                            vir_mid::TypeDecl::Bool
                            | vir_mid::TypeDecl::Int(_)
                            | vir_mid::TypeDecl::Float(_)
                            | vir_mid::TypeDecl::Reference(_)
                            | vir_mid::TypeDecl::Pointer(_)
                            | vir_mid::TypeDecl::Sequence(_) => {
                                // Primitive type. Nothing to do.
                            }
                            vir_mid::TypeDecl::TypeVar(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Tuple(decl) => {
                                // TODO: Remove code duplication.
                                for field in decl.iter_fields() {
                                    let field_place = self.encode_field_place(
                                        ty, &field, place.clone().into(), position
                                    )?;
                                    let field_value = self.obtain_struct_field_snapshot(
                                        ty, &field, value.clone().into(), position
                                    )?;
                                    self.encode_into_memory_block_method(&field.ty)?;
                                    let field_ty = &field.ty;
                                    statements.push(stmtp! {
                                        position =>
                                        call into_memory_block<field_ty>([field_place], root_address, [field_value])
                                    });
                                }
                                self.encode_memory_block_join_method(ty)?;
                                statements.push(stmtp! {
                                    position =>
                                    call memory_block_join<ty>([address.clone()])
                                });
                            },
                            vir_mid::TypeDecl::Struct(decl) => {
                                // TODO: Remove code duplication.
                                for field in decl.iter_fields() {
                                    let field_place = self.encode_field_place(
                                        ty, &field, place.clone().into(), position
                                    )?;
                                    let field_value = self.obtain_struct_field_snapshot(
                                        ty, &field, value.clone().into(), position
                                    )?;
                                    self.encode_into_memory_block_method(&field.ty)?;
                                    let field_ty = &field.ty;
                                    statements.push(stmtp! {
                                        position =>
                                        call into_memory_block<field_ty>([field_place], root_address, [field_value])
                                    });
                                }
                                self.encode_memory_block_join_method(ty)?;
                                statements.push(stmtp! {
                                    position =>
                                    call memory_block_join<ty>([address.clone()])
                                });
                            }
                            vir_mid::TypeDecl::Enum(decl) => {
                                let discriminant_call =
                                    self.obtain_enum_discriminant(value.clone().into(), ty, Default::default())?;
                                let discriminant_field = decl.discriminant_field();
                                let discriminant_place = self.encode_field_place(
                                    ty,
                                    &discriminant_field,
                                    place.clone().into(),
                                    position,
                                )?;
                                let discriminant_value =
                                    self.construct_constant_snapshot(&decl.discriminant_type, discriminant_call.clone(), position)?;
                                let discriminant_type = &decl.discriminant_type;
                                self.encode_into_memory_block_method(discriminant_type)?;
                                statements.push(stmtp! {
                                    position =>
                                    call into_memory_block<discriminant_type>([discriminant_place], root_address, [discriminant_value])
                                });
                                for (&discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants) {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty, &variant_index, place.clone().into(), position,
                                    )?;
                                    let variant_value = self.obtain_enum_variant_snapshot(ty, &variant_index, value.clone().into(), position)?;
                                    let variant_ty = &ty.clone().variant(variant_index);
                                    self.encode_into_memory_block_method(variant_ty)?;
                                    let condition = expr! {
                                        [discriminant_call.clone()] == [discriminant.into()]
                                    };
                                    let condition1 = condition.clone();
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition1> into_memory_block<variant_ty>([variant_place], root_address, [variant_value])
                                    });
                                    self.encode_memory_block_join_method(ty)?;
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition> memory_block_join<ty>([address.clone()], [discriminant.into()])
                                    });
                                }
                            }
                            vir_mid::TypeDecl::Union(decl) => {
                                let discriminant_call =
                                    self.obtain_enum_discriminant(value.clone().into(), ty, Default::default())?;
                                for (&discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants) {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty, &variant_index, place.clone().into(), position,
                                    )?;
                                    let variant_value = self.obtain_enum_variant_snapshot(ty, &variant_index, value.clone().into(), position)?;
                                    let variant_ty = &ty.clone().variant(variant_index);
                                    self.encode_into_memory_block_method(variant_ty)?;
                                    let condition = expr! {
                                        [discriminant_call.clone()] == [discriminant.into()]
                                    };
                                    let condition1 = condition.clone();
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition1> into_memory_block<variant_ty>([variant_place], root_address, [variant_value])
                                    });
                                    self.encode_memory_block_join_method(ty)?;
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition> memory_block_join<ty>([address.clone()], [discriminant.into()])
                                    });
                                }
                            }
                            vir_mid::TypeDecl::Array(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Map(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Never => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
                        };
                    }
                    requires ([ self.acc_owned_non_aliased(ty, place, root_address, value.clone(), lifetimes_copy)? ]);
                    ensures (acc(MemoryBlock([address], [size_of])));
                    ensures (([bytes]) == (Snap<ty>::to_bytes(value)));
            };
            method.body = Some(statements);
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_assign_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: vir_mid::Expression,
        value: vir_mid::Rvalue,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let method_name = self.encode_assign_method_name(target.get_type(), &value)?;
        self.encode_assign_method(&method_name, target.get_type(), &value)?;
        let target_place = self.encode_expression_as_place(&target)?;
        let target_address = self.extract_root_address(&target)?;
        let mut arguments = vec![target_place, target_address];
        self.encode_rvalue_arguments(&mut arguments, &value)?;
        let target_value_type = target.get_type().to_snapshot(self)?;
        let result_value = self.create_new_temporary_variable(target_value_type)?;
        statements.push(vir_low::Statement::method_call(
            method_name,
            arguments,
            vec![result_value.clone().into()],
            position,
        ));
        self.encode_snapshot_update(statements, &target, result_value.clone().into(), position)?;
        if let vir_mid::Rvalue::Ref(value) = value {
            assert!(value.is_mut, "unimplemented!()");
            let final_snapshot = self.reference_target_final_snapshot(
                target.get_type(),
                result_value.into(),
                position,
            )?;
            self.encode_snapshot_update(statements, &value.place, final_snapshot, position)?;
        }
        Ok(())
    }
    fn encode_consume_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        operand: vir_mid::Operand,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let method_name = self.encode_consume_operand_method_name(&operand)?;
        self.encode_consume_operand_method(&method_name, &operand)?;
        let mut arguments = Vec::new();
        self.encode_operand_arguments(&mut arguments, &operand)?;
        statements.push(vir_low::Statement::method_call(
            method_name,
            arguments,
            Vec::new(),
            position,
        ));
        Ok(())
    }

    fn encode_lft_tok_sep_take_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_lft_tok_sep_take_methods
            .contains(&lft_count)
        {
            self.builtin_methods_state
                .encoded_lft_tok_sep_take_methods
                .insert(lft_count);

            self.encode_lifetime_token_predicate()?;
            self.encode_lifetime_included()?;
            self.encode_lifetime_intersect(lft_count)?;
            self.encode_lifetime_included_intersect_axiom(lft_count)?;
            use vir_low::macros::*;

            let method_name = self.encode_lft_tok_sep_take_method_name(lft_count)?;
            var_decls!(rd_perm: Perm);

            // Parameters
            let mut parameters: Vec<vir_low::VariableDecl> =
                self.create_lifetime_var_decls(lft_count)?;

            // Preconditions
            let mut pres = vec![expr! {
                [vir_low::Expression::no_permission()] < rd_perm
            }];
            for lifetime in &parameters {
                pres.push(vir_low::Expression::predicate_access_predicate_no_pos(
                    stringify!(LifetimeToken).to_string(),
                    vec![lifetime.clone().into()],
                    rd_perm.clone().into(),
                ));
            }
            parameters.push(rd_perm.clone());

            // Postconditions
            var_decls!(lft: Lifetime);
            let lifetimes_expr: Vec<vir_low::Expression> =
                self.create_lifetime_expressions(lft_count)?;
            let posts = vec![
                // FIXME: use encode_lifetime_token from prusti-viper/src/encoder/middle/core_proof/lifetimes/interface.rs (to be merged)
                vir_low::Expression::predicate_access_predicate_no_pos(
                    stringify!(LifetimeToken).to_string(),
                    vec![lft.clone().into()],
                    rd_perm.into(),
                ),
                vir_low::Expression::binary_op_no_pos(
                    vir_low::BinaryOpKind::EqCmp,
                    expr! { lft },
                    vir_low::Expression::domain_function_call(
                        "Lifetime",
                        format!("intersect${}", lft_count),
                        lifetimes_expr,
                        ty!(Lifetime),
                    ),
                ),
            ];

            // Create Method
            let method =
                vir_low::MethodDecl::new(method_name, parameters, vec![lft], pres, posts, None);
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_lft_tok_sep_return_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_lft_tok_sep_return_methods
            .contains(&lft_count)
        {
            self.builtin_methods_state
                .encoded_lft_tok_sep_return_methods
                .insert(lft_count);

            self.encode_lifetime_token_predicate()?;
            self.encode_lifetime_included()?;
            self.encode_lifetime_intersect(lft_count)?;
            self.encode_lifetime_included_intersect_axiom(lft_count)?;
            use vir_low::macros::*;

            let method_name = self.encode_lft_tok_sep_return_method_name(lft_count)?;
            var_decls!(lft: Lifetime); // target
            var_decls!(rd_perm: Perm);
            let lifetimes_var: Vec<vir_low::VariableDecl> =
                self.create_lifetime_var_decls(lft_count)?;
            let lifetimes_expr: Vec<vir_low::Expression> =
                self.create_lifetime_expressions(lft_count)?;

            // Parameters
            let mut parameters = vec![lft.clone()];
            parameters.append(lifetimes_var.clone().as_mut());
            parameters.push(rd_perm.clone());

            // Preconditions
            let pres = vec![
                expr! {
                    [vir_low::Expression::no_permission()] < rd_perm
                },
                vir_low::Expression::predicate_access_predicate_no_pos(
                    stringify!(LifetimeToken).to_string(),
                    vec![lft.clone().into()],
                    rd_perm.clone().into(),
                ),
                vir_low::Expression::binary_op_no_pos(
                    vir_low::BinaryOpKind::EqCmp,
                    expr! { lft },
                    vir_low::Expression::domain_function_call(
                        "Lifetime",
                        format!("intersect${}", lft_count),
                        lifetimes_expr,
                        ty!(Lifetime),
                    ),
                ),
            ];

            // Postconditions
            let posts: Vec<vir_low::Expression> = lifetimes_var
                .into_iter()
                .map(|lifetime| {
                    vir_low::Expression::predicate_access_predicate_no_pos(
                        stringify!(LifetimeToken).to_string(),
                        vec![lifetime.into()],
                        rd_perm.clone().into(),
                    )
                })
                .collect();

            // Create Method
            let method =
                vir_low::MethodDecl::new(method_name, parameters, vec![], pres, posts, None);
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_newlft_method(&mut self) -> SpannedEncodingResult<()> {
        if !self.builtin_methods_state.encoded_newlft_method {
            self.builtin_methods_state.encoded_newlft_method = true;
            self.encode_lifetime_token_predicate()?;
            use vir_low::macros::*;
            var_decls!(bw: Lifetime);
            let method = vir_low::MethodDecl::new(
                "newlft",
                Vec::new(),
                vec![bw.clone()],
                Vec::new(),
                vec![expr! { acc(LifetimeToken(bw)) }],
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_endlft_method(&mut self) -> SpannedEncodingResult<()> {
        if !self.builtin_methods_state.encoded_endlft_method {
            self.builtin_methods_state.encoded_endlft_method = true;
            self.encode_lifetime_token_predicate()?;
            use vir_low::macros::*;
            var_decls!(bw: Lifetime);
            let method = vir_low::MethodDecl::new(
                "endlft",
                vec![bw.clone()],
                Vec::new(),
                vec![expr! { acc(LifetimeToken(bw)) }],
                vec![expr! { acc(DeadLifetimeToken(bw)) }],
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_open_close_mut_ref_methods(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_open_close_mut_ref_methods
            .contains(ty)
        {
            self.builtin_methods_state
                .encoded_open_close_mut_ref_methods
                .insert(ty.clone());
            self.encode_lifetime_token_predicate()?;
            use vir_low::macros::*;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let target_type = &type_decl.unwrap_reference().target_type;
            let position = vir_low::Position::default();

            var_decls! {
                lifetime: Lifetime,
                lifetime_perm: Perm,
                place: Place,
                snapshot: {ty.to_snapshot(self)?}
            };
            let deref_place = self.reference_deref_place(place.clone().into(), position)?;
            let address_snapshot =
                self.reference_address_snapshot(ty, snapshot.clone().into(), position)?;
            let current_snapshot =
                self.reference_target_current_snapshot(ty, snapshot.clone().into(), position)?;
            let final_snapshot =
                self.reference_target_final_snapshot(ty, snapshot.clone().into(), position)?;
            let open_method = vir_low::MethodDecl::new(
                method_name! { open_mut_ref<ty> },
                vec![lifetime.clone(), lifetime_perm.clone(), place, snapshot],
                Vec::new(),
                vec![
                    expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                    expr! { acc(LifetimeToken(lifetime), lifetime_perm) },
                    expr! {
                        acc(UniqueRef<target_type>(
                            lifetime,
                            [deref_place.clone()],
                            [address_snapshot.clone()],
                            [current_snapshot.clone()],
                            [final_snapshot.clone()]
                        ))
                    },
                ],
                vec![
                    expr! { acc(OwnedNonAliased<target_type>(
                        [deref_place.clone()],
                        [address_snapshot.clone()],
                        [current_snapshot]
                    ))},
                    // CloseMutRef predicate corresponds to the following
                    // viewshift:
                    // ```
                    // (acc(OwnedNonAliased<target_type>(
                    //     [deref_place],
                    //     [address_snapshot],
                    //     ?current_snapshot
                    // ))) --* (
                    //     (acc(LifetimeToken(lifetime), lifetime_perm)) &&
                    //     (acc(UniqueRef<target_type>(
                    //         lifetime,
                    //         [deref_place],
                    //         [address_snapshot],
                    //         current_snapshot,
                    //         [final_snapshot]
                    //     )))
                    // )
                    // ```
                    expr! { acc(CloseMutRef<target_type>(
                        lifetime,
                        lifetime_perm,
                        [deref_place],
                        [address_snapshot],
                        [final_snapshot]
                    ))},
                ],
                None,
            );
            self.declare_method(open_method)?;

            {
                var_decls! {
                    lifetime: Lifetime,
                    lifetime_perm: Perm,
                    deref_place: Place,
                    address_snapshot: Address,
                    current_snapshot: { target_type.to_snapshot(self)? },
                    final_snapshot: { target_type.to_snapshot(self)? }
                }
                let close_mut_ref_predicate = vir_low::PredicateDecl::new(
                    predicate_name! { CloseMutRef<target_type> },
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        deref_place.clone(),
                        address_snapshot.clone(),
                        final_snapshot.clone(),
                    ],
                    None,
                );
                self.declare_predicate(close_mut_ref_predicate)?;
                // Apply the viewshift encoded in the `CloseMutRef` predicate.
                let close_method = vir_low::MethodDecl::new(
                    method_name! { close_mut_ref<ty> },
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        deref_place.clone(),
                        address_snapshot.clone(),
                        current_snapshot.clone(),
                        final_snapshot.clone(),
                    ],
                    Vec::new(),
                    vec![
                        expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                        expr! { acc(CloseMutRef<target_type>(
                            lifetime,
                            lifetime_perm,
                            deref_place,
                            address_snapshot,
                            final_snapshot
                        ))},
                        expr! { acc(OwnedNonAliased<target_type>(
                            deref_place,
                            address_snapshot,
                            current_snapshot
                        ))},
                    ],
                    vec![
                        expr! { acc(LifetimeToken(lifetime), lifetime_perm) },
                        expr! {
                            acc(UniqueRef<target_type>(
                                lifetime,
                                deref_place,
                                address_snapshot,
                                current_snapshot,
                                final_snapshot
                            ))
                        },
                    ],
                    None,
                );
                self.declare_method(close_method)?;
            }
        }
        Ok(())
    }
}
