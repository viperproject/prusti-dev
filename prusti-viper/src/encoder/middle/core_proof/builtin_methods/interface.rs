use super::helpers::ToAddressWriter;
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
        snapshots::{IntoSnapshot, SnapshotsInterface},
        type_layouts::TypeLayoutsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{expression::ExpressionIterator, identifier::WithIdentifier},
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
    encoded_assign_methods: FxHashSet<String>,
}

trait Private {
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn encode_fully_split_write_address(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_assign_method_name(
        &self,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<String>;
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
    fn encode_assign_method(
        &mut self,
        method_name: &str,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        post_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::Rvalue,
        result: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_operand(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        post_write_statements: &mut Vec<vir_low::Statement>,
        operand_counter: u32,
        operand: &vir_mid::Operand,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn encode_assign_operand_snapshot(
        &mut self,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn encode_fully_split_write_address(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut writer = ToAddressWriter {
            statements,
            position,
        };
        writer.walk_type(ty, (address, value), self)
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
    fn encode_rvalue_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()> {
        match value {
            vir_mid::Rvalue::UnaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.argument)?;
            }
            vir_mid::Rvalue::BinaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.left)?;
                self.encode_operand_arguments(arguments, &value.right)?;
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
            vir_mid::OperandKind::Copy => {
                unimplemented!();
            }
            vir_mid::OperandKind::Move => {
                unimplemented!();
            }
            vir_mid::OperandKind::Constant => {
                arguments.push(self.lower_expression_into_snapshot(&operand.expression)?)
            }
        }
        Ok(())
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
            let mut post_write_statements = vec![stmtp! {
                position => call write_place<ty>(target_place, target_address, result_value)
            }];
            self.encode_assign_method_rvalue(
                &mut parameters,
                &mut pres,
                &mut posts,
                &mut pre_write_statements,
                &mut post_write_statements,
                value,
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
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        pre_write_statements: &mut Vec<vir_low::Statement>,
        post_write_statements: &mut Vec<vir_low::Statement>,
        value: &vir_mid::Rvalue,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let assigned_value = match value {
            vir_mid::Rvalue::UnaryOp(value) => {
                let operand_value = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    pre_write_statements,
                    post_write_statements,
                    1,
                    &value.argument,
                    position,
                )?;
                self.encode_unary_op_call(
                    value.kind,
                    value.argument.expression.get_type(),
                    operand_value.into(),
                    position,
                )?
            }
            vir_mid::Rvalue::BinaryOp(_value) => {
                unimplemented!();
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
        _posts: &mut Vec<vir_low::Expression>,
        _pre_write_statements: &mut Vec<vir_low::Statement>,
        _post_write_statements: &mut Vec<vir_low::Statement>,
        operand_counter: u32,
        operand: &vir_mid::Operand,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        let value = self.encode_assign_operand_snapshot(operand_counter, operand)?;
        let ty = operand.expression.get_type();
        match operand.kind {
            vir_mid::OperandKind::Copy => {
                unimplemented!();
            }
            vir_mid::OperandKind::Move => {
                unimplemented!();
            }
            vir_mid::OperandKind::Constant => {
                parameters.push(value.clone());
                pres.push(self.encode_snapshot_validity_expression(value.clone().into(), ty)?);
            }
        }
        Ok(value)
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
    fn encode_assign_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        target: vir_mid::Expression,
        value: vir_mid::Rvalue,
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
        // TODO: Remove code duplication with encode_copy_place_method
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
            let mut method = method! {
                move_place<ty>(
                    target_place: Place,
                    target_address: Address,
                    source_place: Place,
                    source_address: Address,
                    source_value: {ty.create_snapshot(self)?}
                ) returns ()
                    raw_code {
                        let compute_address_source = expr! { ComputeAddress::compute_address(source_place, source_address) };
                        let bytes = self.encode_memory_block_bytes_expression(compute_address_source, size_of.clone())?;
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
                    }
                    requires (acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_address)), [size_of.clone()])));
                    requires (acc(OwnedNonAliased<ty>(source_place, source_address, source_value)));
                    ensures (acc(OwnedNonAliased<ty>(target_place, target_address, source_value)));
                    ensures (acc(MemoryBlock((ComputeAddress::compute_address(source_place, source_address)), [size_of])));
                    ensures (([bytes]) == (Snap<ty>::to_bytes(source_value)));
            };
            method.body = Some(statements);
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
            let mut method = method! {
                write_place<ty>(
                    place: Place,
                    address: Address,
                    value: {ty.create_snapshot(self)?}
                ) returns ()
                    raw_code {
                        let validity = self.encode_snapshot_validity_expression(value.clone().into(), ty)?;
                        let compute_address = expr! { ComputeAddress::compute_address(place, address) };
                        self.encode_fully_split_memory_block(
                            &mut statements,
                            ty,
                            compute_address.clone(),
                            position,
                        )?;
                        self.encode_fully_split_write_address(
                            &mut statements,
                            ty,
                            compute_address.clone(),
                            value.clone().into(),
                            position,
                        )?;
                        self.encode_fully_fold_owned_non_aliased(
                            &mut statements,
                            ty,
                            place.clone().into(),
                            &Into::<vir_low::Expression>::into(address.clone()),
                            value.clone().into(),
                            position,
                        )?;
                    }
                    requires (acc(MemoryBlock([compute_address], [size_of])));
                    requires ([validity]);
                    ensures (acc(OwnedNonAliased<ty>(place, address, value)));
            };
            method.body = Some(statements);
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
            let mut helper = SplitJoinHelper::new(false);
            helper.walk_type(ty, (), self)?;
            use vir_low::macros::*;
            let method = vir_low::MethodDecl::new(
                method_name! { memory_block_split<ty> },
                vars! { address: Address },
                Vec::new(),
                helper.preconditions,
                helper.postconditions,
                None,
            );
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
            let mut helper = SplitJoinHelper::new(true);
            helper.walk_type(ty, (), self)?;
            self.encode_snapshot_to_bytes_function(ty)?;
            use vir_low::macros::*;
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
            let method = vir_low::MethodDecl::new(
                method_name! { memory_block_join<ty> },
                vars! { address: Address },
                Vec::new(),
                helper.preconditions,
                helper.postconditions,
                None,
            );
            self.declare_method(method)?;
            self.builtin_methods_state
                .encoded_memory_block_join_methods
                .insert(ty.clone());
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
}
