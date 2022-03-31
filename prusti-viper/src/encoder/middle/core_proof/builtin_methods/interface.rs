use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::split_join::SplitJoinHelper,
        compute_address::ComputeAddressInterface,
        errors::ErrorsInterface,
        fold_unfold::FoldUnfoldInterface,
        into_low::IntoLowInterface,
        lowerer::{Lowerer, MethodsLowererInterface, VariablesLowererInterface},
        places::PlacesInterface,
        predicates_memory_block::PredicatesMemoryBlockInterface,
        predicates_owned::PredicatesOwnedInterface,
        snapshots::{
            IntoSnapshot, SnapshotBytesInterface, SnapshotValidityInterface,
            SnapshotValuesInterface, SnapshotVariablesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{expression::ExpressionIterator, identifier::WithIdentifier},
    low::{self as vir_low, operations::ToLow},
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
                arguments.push(self.lower_expression_into_snapshot(&operand.expression)?);
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
        arguments.push(self.lower_expression_into_snapshot(expression)?);
        Ok(())
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
            var_decls! { result_value: {ty.create_snapshot(self)?} };
            let mut pres = vec![
                expr! { acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_address)), [size_of])) },
            ];
            let mut posts = vec![
                expr! { acc(OwnedNonAliased<ty>(target_place, target_address, result_value)) },
            ];
            let mut pre_write_statements = Vec::new();
            let post_write_statements = vec![stmtp! {
                position => call write_place<ty>(target_place, target_address, result_value)
            }];
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
                .encoded_assign_methods
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
            vir_mid::Rvalue::AddressOf(value) => {
                let ty = value.place.get_type();
                var_decls! {
                    operand_place: Place,
                    operand_address: Address,
                    operand_value: { ty.create_snapshot(self)? }
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
            vir_mid::Rvalue::Discriminant(value) => {
                let ty = value.place.get_type();
                var_decls! {
                    operand_place: Place,
                    operand_address: Address,
                    operand_value: { ty.create_snapshot(self)? }
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
                    vir_mid::Type::Struct(_) => {
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
            operand.expression.get_type().create_snapshot(self)?,
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
                    value: {ty.create_snapshot(self)?}
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
                    source_value: {ty.create_snapshot(self)?}
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
                    for (discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.clone().to_low(self)?]
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
                    source_value: {ty.create_snapshot(self)?}
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
                        self.encode_fully_join_memory_block(
                            &mut statements,
                            ty,
                            expr! { ComputeAddress::compute_address(source_place, source_address) },
                            position,
                        )?;
                        statements.push(stmtp! { position => call write_place<ty>(target_place, target_address, source_value)});
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
                value: {ty.create_snapshot(self)?}
            };
            let validity = self.encode_snapshot_valid_call_for_type(value.clone().into(), ty)?;
            let address = expr! { ComputeAddress::compute_address(place, root_address) };
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            match type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_) => {
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
                        unimplemented!()
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
                    for (discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.clone().to_low(self)?]
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
                    for (discriminant_value, variant) in
                        decl.discriminant_values.iter().zip(&decl.variants)
                    {
                        let variant_index = variant.name.clone().into();
                        let condition = expr! {
                            [discriminant_call.clone()] == [discriminant_value.clone().to_low(self)?]
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
            self.mark_owned_non_aliased_as_unfolded(ty)?;
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
                        for (discriminant_value, variant) in enum_decl
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
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
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
                        for (discriminant_value, variant) in enum_decl
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
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
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
                        let discriminant_bounds = enum_decl.discriminant_bounds.to_low(self)?;
                        let mut preconditions = vec![
                            expr! { acc(MemoryBlock([discriminant_address.clone()], [discriminant_size_of.clone()]))},
                            discriminant_bounds.replace_discriminant(&discriminant.clone().into()),
                        ];
                        let to_bytes = ty! { Bytes };
                        let mut bytes_quantifier_conjuncts = Vec::new();
                        let memory_block_bytes = self.encode_memory_block_bytes_expression(
                            address.clone().into(),
                            size_of,
                        )?;
                        let snapshot: vir_low::Expression =
                            var! { snapshot: {ty.create_snapshot(self)?} }.into();
                        for (discriminant_value, variant) in enum_decl
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
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
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
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
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
                                snapshot: {ty.create_snapshot(self)?} ::
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
                        let discriminant_bounds = enum_decl.discriminant_bounds.to_low(self)?;
                        let mut preconditions =
                            vec![discriminant_bounds
                                .replace_discriminant(&discriminant.clone().into())];
                        let to_bytes = ty! { Bytes };
                        let mut bytes_quantifier_conjuncts = Vec::new();
                        let memory_block_bytes = self.encode_memory_block_bytes_expression(
                            address.clone().into(),
                            size_of,
                        )?;
                        let snapshot: vir_low::Expression =
                            var! { snapshot: {ty.create_snapshot(self)?} }.into();
                        for (discriminant_value, variant) in enum_decl
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
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
                                (acc(MemoryBlock([variant_address.clone()], [variant_size_of.clone()])))
                            });
                            let memory_block_variant_bytes = self
                                .encode_memory_block_bytes_expression(
                                    variant_address,
                                    variant_size_of,
                                )?;
                            bytes_quantifier_conjuncts.push(expr! {
                                (discriminant == [discriminant_value.clone().to_low(self)?]) ==>
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
                                snapshot: {ty.create_snapshot(self)?} ::
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
                        snapshot: {ty.create_snapshot(self)?} ::
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
            let size_of = self.encode_type_size_expression(ty)?;
            let compute_address = ty!(Address);
            let to_bytes = ty! { Bytes };
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::IntoMemoryBlock),
            );
            let mut statements = Vec::new();
            let mut method = method! {
                into_memory_block<ty>(
                    place: Place,
                    root_address: Address,
                    value: {ty.create_snapshot(self)?}
                ) returns ()
                    raw_code {
                        let address = expr! {
                            ComputeAddress::compute_address(place, root_address)
                        };
                        let bytes = self.encode_memory_block_bytes_expression(
                            address.clone(), size_of.clone()
                        )?;
                        let type_decl = self.encoder.get_type_decl_mid(ty)?;
                        statements.push(stmtp! {
                            position =>
                            unfold OwnedNonAliased<ty>(place, root_address, value)
                        });
                        match type_decl {
                            vir_mid::TypeDecl::Bool
                            | vir_mid::TypeDecl::Int(_)
                            | vir_mid::TypeDecl::Float(_)
                            | vir_mid::TypeDecl::Pointer(_) => {
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
                                for (discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants) {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty, &variant_index, place.clone().into(), position,
                                    )?;
                                    let variant_value = self.obtain_enum_variant_snapshot(ty, &variant_index, value.clone().into(), position)?;
                                    let variant_ty = &ty.clone().variant(variant_index);
                                    self.encode_into_memory_block_method(variant_ty)?;
                                    let condition = expr! {
                                        [discriminant_call.clone()] == [discriminant.clone().to_low(self)?]
                                    };
                                    let condition1 = condition.clone();
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition1> into_memory_block<variant_ty>([variant_place], root_address, [variant_value])
                                    });
                                    self.encode_memory_block_join_method(ty)?;
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition> memory_block_join<ty>([address.clone()], [discriminant.clone().to_low(self)?])
                                    });
                                }
                            }
                            vir_mid::TypeDecl::Union(decl) => {
                                let discriminant_call =
                                    self.obtain_enum_discriminant(value.clone().into(), ty, Default::default())?;
                                for (discriminant, variant) in decl.discriminant_values.iter().zip(&decl.variants) {
                                    let variant_index = variant.name.clone().into();
                                    let variant_place = self.encode_enum_variant_place(
                                        ty, &variant_index, place.clone().into(), position,
                                    )?;
                                    let variant_value = self.obtain_enum_variant_snapshot(ty, &variant_index, value.clone().into(), position)?;
                                    let variant_ty = &ty.clone().variant(variant_index);
                                    self.encode_into_memory_block_method(variant_ty)?;
                                    let condition = expr! {
                                        [discriminant_call.clone()] == [discriminant.clone().to_low(self)?]
                                    };
                                    let condition1 = condition.clone();
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition1> into_memory_block<variant_ty>([variant_place], root_address, [variant_value])
                                    });
                                    self.encode_memory_block_join_method(ty)?;
                                    statements.push(stmtp! {
                                        position =>
                                        call<condition> memory_block_join<ty>([address.clone()], [discriminant.clone().to_low(self)?])
                                    });
                                }
                            }
                            vir_mid::TypeDecl::Array(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Reference(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Never => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Closure(_) => unimplemented!("ty: {}", ty),
                            vir_mid::TypeDecl::Unsupported(_) => unimplemented!("ty: {}", ty),
                        };
                    }
                    requires (acc(OwnedNonAliased<ty>(place, root_address, value)));
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
        let target_value_type = target.get_type().create_snapshot(self)?;
        let result_value = self.create_new_temporary_variable(target_value_type)?;
        statements.push(vir_low::Statement::method_call(
            method_name,
            arguments,
            vec![result_value.clone().into()],
            position,
        ));
        self.encode_snapshot_update(statements, &target, result_value.into(), position)?;
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
}
