use super::{
    builders::{
        ChangeUniqueRefPlaceMethodBuilder, DuplicateFracRefMethodBuilder,
        MemoryBlockCopyMethodBuilder,
    },
    BuiltinMethodCallsInterface, CallContext,
};
use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        block_markers::BlockMarkersInterface,
        builtin_methods::builders::{
            BuiltinMethodBuilderMethods, CopyPlaceMethodBuilder, IntoMemoryBlockMethodBuilder,
            MemoryBlockJoinMethodBuilder, MemoryBlockSplitMethodBuilder, MovePlaceMethodBuilder,
            WriteAddressConstantMethodBuilder, WritePlaceConstantMethodBuilder,
        },
        compute_address::ComputeAddressInterface,
        errors::ErrorsInterface,
        lifetimes::LifetimesInterface,
        lowerer::{
            DomainsLowererInterface, Lowerer, MethodsLowererInterface, PredicatesLowererInterface,
            VariablesLowererInterface,
        },
        places::PlacesInterface,
        predicates::{
            OwnedNonAliasedUseBuilder, PredicatesMemoryBlockInterface, PredicatesOwnedInterface,
        },
        references::ReferencesInterface,
        snapshots::{
            BuiltinFunctionsInterface, IntoBuiltinMethodSnapshot, IntoProcedureFinalSnapshot,
            IntoProcedureSnapshot, IntoPureSnapshot, IntoSnapshot, SnapshotBytesInterface,
            SnapshotValidityInterface, SnapshotValuesInterface, SnapshotVariablesInterface,
        },
        type_layouts::TypeLayoutsInterface,
    },
};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use vir_crate::{
    common::{
        expression::{ExpressionIterator, UnaryOperationHelpers},
        identifier::WithIdentifier,
    },
    low::{self as vir_low, macros::method_name},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes, ty::Typed},
    },
};

#[derive(Default)]
pub(in super::super) struct BuiltinMethodsState {
    encoded_write_place_constant_methods: FxHashSet<String>,
    encoded_move_place_methods: FxHashSet<String>,
    encoded_copy_place_methods: FxHashSet<String>,
    encoded_change_unique_ref_place_method: FxHashSet<String>,
    encoded_duplicate_frac_ref_method: FxHashSet<String>,
    encoded_write_address_constant_methods: FxHashSet<String>,
    encoded_owned_non_aliased_havoc_methods: FxHashSet<String>,
    encoded_memory_block_copy_methods: FxHashSet<String>,
    encoded_memory_block_split_methods: FxHashSet<String>,
    encoded_memory_block_join_methods: FxHashSet<String>,
    encoded_memory_block_havoc_methods: FxHashSet<String>,
    encoded_into_memory_block_methods: FxHashSet<String>,
    encoded_assign_methods: FxHashSet<String>,
    encoded_consume_operand_methods: FxHashSet<String>,
    encoded_newlft_method: bool,
    encoded_endlft_method: bool,
    encoded_open_frac_bor_atomic_methods: FxHashSet<String>,
    encoded_dead_inclusion_method: bool,
    encoded_lft_tok_sep_take_methods: FxHashSet<usize>,
    encoded_lft_tok_sep_return_methods: FxHashSet<usize>,
    encoded_open_close_mut_ref_methods: FxHashSet<String>,
    encoded_bor_shorten_methods: FxHashSet<String>,
}

trait Private {
    fn encode_rvalue_arguments(
        &mut self,
        target: &vir_mid::Expression,
        arguments: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()>;
    fn encode_operand_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        operand: &vir_mid::Operand,
        encode_lifetime_arguments: bool,
    ) -> SpannedEncodingResult<()>;
    fn encode_place_arguments_with_permission(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        expression: &vir_mid::Expression,
        ty: &vir_mid::Type,
        permission: &Option<vir_mid::VariableDecl>,
    ) -> SpannedEncodingResult<()>;
    fn encode_place_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        expression: &vir_mid::Expression,
        encode_lifetime_arguments: bool,
    ) -> SpannedEncodingResult<()>;
    fn encode_open_frac_bor_atomic_method_name(
        &self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
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
    fn encode_havoc_owned_non_aliased_method_name(
        &self,
        ty: &vir_mid::Type,
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
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
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
        value: &vir_mid::ast::rvalue::CheckedBinaryOp,
        ty: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_method_rvalue_reborrow(
        &mut self,
        method_name: &str,
        parameters: Vec<vir_low::VariableDecl>,
        pres: Vec<vir_low::Expression>,
        posts: Vec<vir_low::Expression>,
        value: &vir_mid::ast::rvalue::Reborrow,
        ty: &vir_mid::Type,
        result_value: vir_low::VariableDecl,
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
        result_type: &vir_mid::Type,
        result_value: vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::too_many_arguments)]
    fn encode_assign_operand(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        operand_counter: u32,
        operand: &vir_mid::Operand,
        position: vir_low::Position,
        add_lifetime_parameters: bool,
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
        target: &vir_mid::Expression,
        arguments: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()> {
        match value {
            vir_mid::Rvalue::Repeat(value) => {
                self.encode_operand_arguments(arguments, &value.argument, true)?;
                arguments.push(value.count.into());
            }
            vir_mid::Rvalue::Reborrow(value) => {
                let deref_lifetime = self
                    .encode_lifetime_const_into_procedure_variable(value.deref_lifetime.clone())?;
                let new_borrow_lifetime = self.encode_lifetime_const_into_procedure_variable(
                    value.new_borrow_lifetime.clone(),
                )?;
                let perm_amount = value
                    .lifetime_token_permission
                    .to_procedure_snapshot(self)?;
                self.encode_place_arguments(arguments, &value.deref_place, false)?;
                if value.uniqueness.is_unique() {
                    let snapshot_final = value.deref_place.to_procedure_final_snapshot(self)?;
                    arguments.push(snapshot_final);
                }
                arguments.extend(self.create_lifetime_arguments(
                    CallContext::Procedure,
                    value.deref_place.get_type(),
                )?);
                arguments.push(deref_lifetime.into());
                arguments.push(new_borrow_lifetime.into());
                arguments.push(perm_amount);
            }
            vir_mid::Rvalue::Ref(value) => {
                let new_borrow_lifetime = self.encode_lifetime_const_into_procedure_variable(
                    value.new_borrow_lifetime.clone(),
                )?;
                let perm_amount = value
                    .lifetime_token_permission
                    .to_procedure_snapshot(self)?;
                self.encode_place_arguments(arguments, &value.place, true)?;
                arguments.push(new_borrow_lifetime.into());
                arguments.push(perm_amount);
            }
            vir_mid::Rvalue::AddressOf(value) => {
                self.encode_place_arguments(arguments, &value.place, true)?;
            }
            vir_mid::Rvalue::Len(len_value) => {
                let ty = len_value.place.get_type();
                let len = if ty.is_array() {
                    ty.get_const_arguments()
                        .pop()
                        .unwrap()
                        .to_procedure_snapshot(self)?
                } else {
                    let current_snapshot = len_value.place.to_procedure_snapshot(self)?;
                    let snapshot_length =
                        self.obtain_array_len_snapshot(current_snapshot, Default::default())?;
                    let size_type = self.size_type_mid()?;
                    self.construct_constant_snapshot(
                        &size_type,
                        snapshot_length,
                        Default::default(),
                    )?
                };
                arguments.push(len);
            }
            vir_mid::Rvalue::UnaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.argument, true)?;
            }
            vir_mid::Rvalue::BinaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.left, true)?;
                self.encode_operand_arguments(arguments, &value.right, true)?;
            }
            vir_mid::Rvalue::CheckedBinaryOp(value) => {
                self.encode_operand_arguments(arguments, &value.left, true)?;
                self.encode_operand_arguments(arguments, &value.right, true)?;
            }
            vir_mid::Rvalue::Discriminant(value) => {
                let ty = if let vir_mid::Type::Reference(ty) = value.place.get_type() {
                    &ty.target_type
                } else {
                    value.place.get_type()
                };
                self.encode_place_arguments_with_permission(
                    arguments,
                    &value.place,
                    ty,
                    &value.source_permission,
                )?;
            }
            vir_mid::Rvalue::Aggregate(aggr_value) => {
                // For aggregates, we take the lifetimes of the target, not of
                // the operands.
                arguments.extend(
                    self.create_lifetime_arguments(CallContext::Procedure, target.get_type())?,
                );
                for operand in &aggr_value.operands {
                    self.encode_operand_arguments(arguments, operand, false)?;
                }
            }
        }
        Ok(())
    }
    fn encode_operand_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        operand: &vir_mid::Operand,
        encode_lifetime_arguments: bool,
    ) -> SpannedEncodingResult<()> {
        match operand.kind {
            vir_mid::OperandKind::Copy | vir_mid::OperandKind::Move => {
                self.encode_place_arguments(
                    arguments,
                    &operand.expression,
                    encode_lifetime_arguments,
                )?;
            }
            vir_mid::OperandKind::Constant => {
                arguments.push(operand.expression.to_procedure_snapshot(self)?);
            }
        }
        Ok(())
    }
    fn encode_place_arguments_with_permission(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        place: &vir_mid::Expression,
        ty: &vir_mid::Type,
        permission: &Option<vir_mid::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        arguments.push(self.encode_expression_as_place(place)?);
        arguments.push(self.extract_root_address(place)?);
        if let Some(variable) = permission {
            arguments.push(variable.to_procedure_snapshot(self)?.into());
        } else {
            arguments.push(vir_low::Expression::full_permission());
        }
        arguments.push(place.to_procedure_snapshot(self)?);
        arguments.extend(self.create_lifetime_arguments(CallContext::Procedure, ty)?);
        Ok(())
    }
    fn encode_place_arguments(
        &mut self,
        arguments: &mut Vec<vir_low::Expression>,
        expression: &vir_mid::Expression,
        encode_lifetime_arguments: bool,
    ) -> SpannedEncodingResult<()> {
        arguments.push(self.encode_expression_as_place(expression)?);
        arguments.push(self.extract_root_address(expression)?);
        arguments.push(expression.to_procedure_snapshot(self)?);
        if encode_lifetime_arguments {
            arguments.extend(
                self.create_lifetime_arguments(CallContext::Procedure, expression.get_type())?,
            );
        }
        Ok(())
    }
    fn encode_open_frac_bor_atomic_method_name(
        &self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("frac_bor_atomic_acc${}", ty.get_identifier()))
    }
    fn encode_lft_tok_sep_take_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("lft_tok_sep_take${lft_count}"))
    }
    fn encode_lft_tok_sep_return_method_name(
        &self,
        lft_count: usize,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("lft_tok_sep_return${lft_count}"))
    }
    fn encode_assign_method_name(
        &self,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<String> {
        Ok(format!(
            "assign${}${}$${}${}${}",
            ty.get_identifier(),
            value.get_identifier(),
            value
                .get_lifetimes()
                .into_iter()
                .map(|lifetime| lifetime.to_string())
                .join("$"),
            value
                .get_const_arguments()
                .into_iter()
                .map(|arg| arg.to_string())
                .join("$"),
            ty.get_const_arguments()
                .into_iter()
                .map(|arg| arg.to_string())
                .join("$"),
        ))
    }
    fn encode_consume_operand_method_name(
        &self,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("consume${}", operand.get_identifier()))
    }
    fn encode_havoc_owned_non_aliased_method_name(
        &self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("havoc_owned${}", ty.get_identifier()))
    }
    fn encode_assign_method(
        &mut self,
        method_name: &str,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<()> {
        // FIXME: For encoding the assign, we should use `RValueDecl` similarly
        // to how other methods use `TypeDecl` for encoding. Currently we use
        // value and, as a result, may encode the method in not general enough
        // way and get a conflict.
        if !self
            .builtin_methods_state
            .encoded_assign_methods
            .contains(method_name)
        {
            self.builtin_methods_state
                .encoded_assign_methods
                .insert(method_name.to_string());

            self.encode_compute_address(ty)?;
            self.mark_owned_non_aliased_as_unfolded(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::MovePlace),
            );
            use vir_low::macros::*;
            let compute_address = ty!(Address);
            let size_of = self.encode_type_size_expression2(ty, ty)?;
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
            match value {
                vir_mid::Rvalue::CheckedBinaryOp(value) => {
                    self.encode_assign_method_rvalue_checked_binary_op(
                        &mut parameters,
                        &mut pres,
                        &mut posts,
                        value,
                        ty,
                        &result_value,
                        position,
                    )?;
                }
                vir_mid::Rvalue::Reborrow(value) => {
                    self.encode_assign_method_rvalue_reborrow(
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
                    let mut lifetimes_ty: Vec<vir_low::Expression> = vec![];
                    for lifetime in ty.get_lifetimes() {
                        let snap = self.encode_lifetime_const_into_procedure_variable(lifetime)?;
                        lifetimes_ty.push(snap.into());
                    }
                    let predicate = self.owned_non_aliased_full_vars(
                        CallContext::BuiltinMethod,
                        ty,
                        ty,
                        &target_place,
                        &target_address,
                        &result_value,
                    )?;
                    posts.push(predicate);
                    self.encode_assign_method_rvalue(
                        &mut parameters,
                        &mut pres,
                        &mut posts,
                        value,
                        ty,
                        &result_value,
                        position,
                    )?;
                }
            }
            // It seems that we do not have proper primitives into which we
            // could desugar `assign`.
            let body = None;
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::MirOperation,
                parameters,
                vec![result_value],
                pres,
                posts,
                body,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_consume_operand_method(
        &mut self,
        method_name: &str,
        operand: &vir_mid::Operand,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if !self
            .builtin_methods_state
            .encoded_consume_operand_methods
            .contains(method_name)
        {
            self.builtin_methods_state
                .encoded_consume_operand_methods
                .insert(method_name.to_string());
            let mut parameters = Vec::new();
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            self.encode_assign_operand(
                &mut parameters,
                &mut pres,
                &mut posts,
                1,
                operand,
                position,
                true,
            )?;
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::MirOperation,
                parameters,
                Vec::new(),
                pres,
                posts,
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_assign_method_rvalue(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
        value: &vir_mid::Rvalue,
        result_type: &vir_mid::Type,
        result_value: &vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let assigned_value = match value {
            vir_mid::Rvalue::Repeat(value) => {
                let operand_value = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    1,
                    &value.argument,
                    position,
                    true,
                )?;
                var_decls! { count: Int };
                parameters.push(count.clone());
                pres.push(expr! { [0.into()] <= count });
                self.encode_sequence_repeat_constructor_call(
                    result_type,
                    operand_value.into(),
                    count.into(),
                )?
            }
            vir_mid::Rvalue::Reborrow(_value) => {
                unreachable!("Reborrow should be handled in the caller.");
            }
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
                let predicate = self.owned_non_aliased_full_vars(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    &operand_place,
                    &operand_address,
                    &operand_value,
                )?;
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
            vir_mid::Rvalue::Len(_value) => {
                var_decls! { length: {self.size_type()?} };
                parameters.push(length.clone());
                length.into()
            }
            vir_mid::Rvalue::UnaryOp(value) => {
                let operand_value = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    1,
                    &value.argument,
                    position,
                    true,
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
                    1,
                    &value.left,
                    position,
                    true,
                )?;
                let operand_right = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    2,
                    &value.right,
                    position,
                    true,
                )?;
                if value.kind == vir_mid::BinaryOpKind::Div {
                    // For some reason, division is not CheckedBinaryOp, but the
                    // regular one. Therefore, we need to put the checks for
                    // overflows into the precondition.
                    let type_decl = self.encoder.get_type_decl_mid(result_type)?.unwrap_int();
                    if let Some(lower) = type_decl.lower_bound {
                        let zero =
                            self.construct_constant_snapshot(result_type, 0.into(), position)?;
                        pres.push(expr! {operand_right != [zero]});
                        let minus_one =
                            self.construct_constant_snapshot(result_type, (-1).into(), position)?;
                        let lower_snap = lower.to_builtin_method_snapshot(self)?;
                        let min =
                            self.construct_constant_snapshot(result_type, lower_snap, position)?;
                        pres.push(
                            expr! {((operand_right != [minus_one]) || (operand_left != [min]))},
                        );
                    }
                }
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
                    operand_permission: Perm,
                    operand_value: { ty.to_snapshot(self)? }
                };
                let predicate = self.owned_non_aliased(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    operand_place.clone().into(),
                    operand_address.clone().into(),
                    operand_value.clone().into(),
                    Some(operand_permission.clone().into()),
                )?;
                pres.push(expr! {
                    [vir_low::Expression::no_permission()] < operand_permission
                });
                pres.push(predicate.clone());
                posts.push(predicate);
                parameters.push(operand_place);
                parameters.push(operand_address);
                parameters.push(operand_permission);
                parameters.push(operand_value.clone());
                parameters.extend(self.create_lifetime_parameters(ty)?);
                pres.push(
                    self.encode_snapshot_valid_call_for_type(operand_value.clone().into(), ty)?,
                );
                let discriminant_call =
                    self.obtain_enum_discriminant(operand_value.into(), ty, position)?;
                self.construct_constant_snapshot(result_type, discriminant_call, position)?
            }
            vir_mid::Rvalue::Aggregate(value) => {
                // For aggregates, we take the lifetimes of the target, not of
                // the operands.
                parameters.extend(self.create_lifetime_parameters(result_type)?);
                let mut arguments = Vec::new();
                for (i, operand) in value.operands.iter().enumerate() {
                    let operand_value = self.encode_assign_operand(
                        parameters,
                        pres,
                        posts,
                        i.try_into().unwrap(),
                        operand,
                        position,
                        false,
                    )?;
                    arguments.push(operand_value.into());
                }
                let assigned_value = match &value.ty {
                    vir_mid::Type::Enum(_) => {
                        let variant_constructor =
                            self.construct_struct_snapshot(&value.ty, arguments, position)?;
                        self.construct_enum_snapshot(&value.ty, variant_constructor, position)?
                    }
                    vir_mid::Type::Struct(_) => {
                        self.construct_struct_snapshot(&value.ty, arguments, position)?
                    }
                    vir_mid::Type::Array(value_ty) => vir_low::Expression::container_op(
                        vir_low::ContainerOpKind::SeqConstructor,
                        vir_low::Type::seq(value_ty.element_type.to_snapshot(self)?),
                        arguments,
                        position,
                    ),
                    ty => unimplemented!("{}", ty),
                };
                posts.push(
                    self.encode_snapshot_valid_call_for_type(assigned_value.clone(), result_type)?,
                );
                assigned_value
            }
        };
        posts.push(exprp! { position => result_value == [assigned_value]});
        posts.push(
            self.encode_snapshot_valid_call_for_type(result_value.clone().into(), result_type)?,
        );
        Ok(())
    }
    fn encode_assign_method_rvalue_checked_binary_op(
        &mut self,
        parameters: &mut Vec<vir_low::VariableDecl>,
        pres: &mut Vec<vir_low::Expression>,
        posts: &mut Vec<vir_low::Expression>,
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
        let type_decl = self.encoder.get_type_decl_mid(ty)?.unwrap_struct();
        let (operation_result_field, flag_field) = {
            let mut iter = type_decl.fields.iter();
            (iter.next().unwrap(), iter.next().unwrap())
        };
        let flag_place =
            self.encode_field_place(ty, flag_field, target_place.clone().into(), position)?;
        let flag_value = self.obtain_struct_field_snapshot(
            ty,
            flag_field,
            result_value.clone().into(),
            position,
        )?;
        let result_address =
            expr! { (ComputeAddress::compute_address(target_place, target_address)) };
        let operation_result_address = self.encode_field_address(
            ty,
            operation_result_field,
            result_address.clone(),
            position,
        )?;
        let operation_result_value = self.obtain_struct_field_snapshot(
            ty,
            operation_result_field,
            result_value.clone().into(),
            position,
        )?;
        let flag_type = &vir_mid::Type::Bool;
        let operation_result_type = value.kind.get_result_type(value.left.expression.get_type());
        let size_of_result =
            self.encode_type_size_expression2(operation_result_type, operation_result_type)?;
        let size_of_padding = self.encode_type_padding_size_expression(ty)?;
        self.encode_memory_block_split_method(ty)?;
        self.encode_write_address_constant_method(operation_result_type)?;
        self.encode_write_place_constant_method(flag_type)?;
        posts.push(expr! { acc(MemoryBlock([result_address], [size_of_padding])) });
        posts.push(
            expr! { acc(MemoryBlock([operation_result_address.clone()], [size_of_result.clone()])) },
        );
        posts.push(
            expr! { acc(OwnedNonAliased<flag_type>([flag_place], target_address, [flag_value.clone()])) },
        );
        let operand_left =
            self.encode_assign_operand(parameters, pres, posts, 1, &value.left, position, true)?;
        let operand_right =
            self.encode_assign_operand(parameters, pres, posts, 2, &value.right, position, true)?;
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
        let operation_result_value_condition = expr! {
            [validity] ==> ([operation_result_value.clone()] == [operation_result])
        };
        let flag_value_condition = expr! {
            [flag_value] == [flag_result]
        };
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
    fn encode_assign_method_rvalue_reborrow(
        &mut self,
        method_name: &str,
        mut parameters: Vec<vir_low::VariableDecl>,
        mut pres: Vec<vir_low::Expression>,
        mut posts: Vec<vir_low::Expression>,
        value: &vir_mid::ast::rvalue::Reborrow,
        result_type: &vir_mid::Type,
        result_value: vir_low::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let reference_type = result_type.clone().unwrap_reference();
        let ty = value.deref_place.get_type();
        var_decls! {
            target_place: Place,
            target_address: Address,
            operand_place: Place,
            operand_root_address: Address,
            operand_snapshot_current: { ty.to_snapshot(self)? },
            operand_snapshot_final: { ty.to_snapshot(self)? }, // use only for unique references
            lifetime_perm: Perm
        };
        let new_borrow_lifetime = value.new_borrow_lifetime.to_pure_snapshot(self)?;
        let deref_lifetime = value.deref_lifetime.to_pure_snapshot(self)?;
        let lifetime_token =
            self.encode_lifetime_token(new_borrow_lifetime.clone(), lifetime_perm.clone().into())?;
        let deref_predicate = if reference_type.uniqueness.is_unique() {
            self.unique_ref_full_vars(
                CallContext::BuiltinMethod,
                ty,
                ty,
                &operand_place,
                &operand_root_address,
                &operand_snapshot_current,
                &operand_snapshot_final,
                &deref_lifetime,
            )?
        } else {
            self.frac_ref_full_vars(
                CallContext::BuiltinMethod,
                ty,
                ty,
                &operand_place,
                &operand_root_address,
                &operand_snapshot_current,
                &deref_lifetime,
            )?
        };
        let valid_result =
            self.encode_snapshot_valid_call_for_type(result_value.clone().into(), result_type)?;
        let new_reference_predicate = {
            self.mark_owned_non_aliased_as_unfolded(result_type)?;
            let mut builder = OwnedNonAliasedUseBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.into(),
                target_address.into(),
                result_value.clone().into(),
            )?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        };
        let restoration = {
            let final_snapshot = self.reference_target_final_snapshot(
                result_type,
                result_value.clone().into(),
                position,
            )?;
            let validity = self.encode_snapshot_valid_call_for_type(final_snapshot, ty)?;
            if reference_type.uniqueness.is_unique() {
                expr! {
                    wand(
                        (acc(DeadLifetimeToken(new_borrow_lifetime))) --* (
                            [deref_predicate.clone()] &&
                            [validity] &&
                            // DeadLifetimeToken is duplicable and does not get consumed.
                            (acc(DeadLifetimeToken(new_borrow_lifetime)))
                        )
                    )
                }
            } else {
                deref_predicate.clone()
            }
        };
        let reference_target_address =
            self.reference_address(result_type, result_value.clone().into(), position)?;
        posts.push(expr! {
            operand_root_address == [reference_target_address]
        });
        let reference_target_current_snapshot = self.reference_target_current_snapshot(
            result_type,
            result_value.clone().into(),
            position,
        )?;
        posts.push(expr! {
            operand_snapshot_current == [reference_target_current_snapshot]
        });
        let reference_target_final_snapshot = self.reference_target_final_snapshot(
            result_type,
            result_value.clone().into(),
            position,
        )?;
        if reference_type.uniqueness.is_unique() {
            posts.push(expr! {
                operand_snapshot_final == [reference_target_final_snapshot]
            });
        }
        pres.push(expr! {
            [vir_low::Expression::no_permission()] < lifetime_perm
        });
        pres.push(expr! {
            lifetime_perm < [vir_low::Expression::full_permission()]
        });
        self.encode_lifetime_included()?;
        let included = ty! { Bool };
        pres.push(expr! {
            Lifetime::included(new_borrow_lifetime, deref_lifetime)
        });
        pres.push(deref_predicate);
        pres.push(lifetime_token.clone());
        posts.push(lifetime_token);
        posts.push(new_reference_predicate);
        posts.push(valid_result);
        posts.push(restoration);
        parameters.push(operand_place);
        parameters.push(operand_root_address);
        parameters.push(operand_snapshot_current);
        if reference_type.uniqueness.is_unique() {
            parameters.push(operand_snapshot_final);
        }
        parameters.extend(self.create_lifetime_parameters(ty)?);
        parameters.push(deref_lifetime);
        parameters.push(new_borrow_lifetime);
        parameters.push(lifetime_perm);
        let method = vir_low::MethodDecl::new(
            method_name,
            vir_low::MethodKind::MirOperation,
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
            operand_root_address: Address,
            operand_snapshot: { ty.to_snapshot(self)? },
            lifetime_perm: Perm
        };
        let new_borrow_lifetime = value.new_borrow_lifetime.to_pure_snapshot(self)?;
        let lifetime_token =
            self.encode_lifetime_token(new_borrow_lifetime.clone(), lifetime_perm.clone().into())?;
        let predicate = self.owned_non_aliased_full_vars(
            CallContext::BuiltinMethod,
            ty,
            ty,
            &operand_place,
            &operand_root_address,
            &operand_snapshot,
        )?;
        let reference_predicate = {
            self.mark_owned_non_aliased_as_unfolded(result_type)?;
            let mut builder = OwnedNonAliasedUseBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.into(),
                target_address.into(),
                result_value.clone().into(),
            )?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            builder.build()
        };
        let restoration = {
            let restoration_snapshot = if value.uniqueness.is_unique() {
                self.reference_target_final_snapshot(
                    result_type,
                    result_value.clone().into(),
                    position,
                )?
            } else {
                self.reference_target_current_snapshot(
                    result_type,
                    result_value.clone().into(),
                    position,
                )?
            };
            let restored_predicate = self.owned_non_aliased(
                CallContext::BuiltinMethod,
                ty,
                ty,
                operand_place.clone().into(),
                operand_root_address.clone().into(),
                restoration_snapshot.clone(),
                None,
            )?;
            let validity = self.encode_snapshot_valid_call_for_type(restoration_snapshot, ty)?;
            expr! {
                wand(
                    (acc(DeadLifetimeToken(new_borrow_lifetime))) --* (
                        [restored_predicate] &&
                        [validity] &&
                        // DeadLifetimeToken is duplicable and does not get consumed.
                        (acc(DeadLifetimeToken(new_borrow_lifetime)))
                    )
                )
            }
        };
        let reference_target_address =
            self.reference_address(result_type, result_value.clone().into(), position)?;
        posts.push(expr! {
            operand_root_address == [reference_target_address]
        });
        // Note: We do not constraint the final snapshot, because it is fresh.
        let reference_target_current_snapshot = self.reference_target_current_snapshot(
            result_type,
            result_value.clone().into(),
            position,
        )?;
        posts.push(expr! {
            operand_snapshot == [reference_target_current_snapshot]
        });
        pres.push(expr! {
            [vir_low::Expression::no_permission()] < lifetime_perm
        });
        pres.push(expr! {
            lifetime_perm < [vir_low::Expression::full_permission()]
        });
        pres.push(predicate);
        pres.push(lifetime_token.clone());
        let operand_validity =
            self.encode_snapshot_valid_call_for_type(operand_snapshot.clone().into(), ty)?;
        pres.push(operand_validity);
        let result_validity =
            self.encode_snapshot_valid_call_for_type(result_value.clone().into(), result_type)?;
        posts.push(lifetime_token);
        posts.push(reference_predicate);
        posts.push(restoration);
        posts.push(result_validity);
        parameters.push(operand_place);
        parameters.push(operand_root_address);
        parameters.push(operand_snapshot);
        parameters.extend(self.create_lifetime_parameters(ty)?);
        parameters.push(new_borrow_lifetime);
        parameters.push(lifetime_perm);
        let method = vir_low::MethodDecl::new(
            method_name,
            vir_low::MethodKind::MirOperation,
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
        operand_counter: u32,
        operand: &vir_mid::Operand,
        _position: vir_low::Position,
        add_lifetime_parameters: bool,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        use vir_low::macros::*;
        let snapshot = self.encode_assign_operand_snapshot(operand_counter, operand)?;
        let ty = operand.expression.get_type();
        match operand.kind {
            vir_mid::OperandKind::Copy | vir_mid::OperandKind::Move => {
                let place = self.encode_assign_operand_place(operand_counter)?;
                let root_address = self.encode_assign_operand_address(operand_counter)?;
                let predicate = self.owned_non_aliased_full_vars(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    &place,
                    &root_address,
                    &snapshot,
                )?;
                pres.push(predicate.clone());
                let post_predicate = if operand.kind == vir_mid::OperandKind::Copy {
                    predicate
                } else {
                    let compute_address = ty!(Address);
                    let size_of = self.encode_type_size_expression2(ty, ty)?;
                    expr! { acc(MemoryBlock((ComputeAddress::compute_address(place, root_address)), [size_of])) }
                };
                posts.push(post_predicate);
                parameters.push(place);
                parameters.push(root_address);
                parameters.push(snapshot.clone());
                if add_lifetime_parameters {
                    parameters.extend(self.create_lifetime_parameters(ty)?);
                }
                // FIXME: We can extract only const generic arguments from ty,
                // not parameters. For parameters we need type_decl.
                // parameters.extend(self.create_const_parameters(&ty)?);
            }
            vir_mid::OperandKind::Constant => {
                parameters.push(snapshot.clone());
            }
        }
        pres.push(self.encode_snapshot_valid_call_for_type(snapshot.clone().into(), ty)?);
        Ok(snapshot)
    }
    fn encode_assign_operand_place(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{operand_counter}_place"),
            self.place_type()?,
        ))
    }
    fn encode_assign_operand_address(
        &mut self,
        operand_counter: u32,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{operand_counter}_root_address"),
            self.address_type()?,
        ))
    }
    fn encode_assign_operand_snapshot(
        &mut self,
        operand_counter: u32,
        operand: &vir_mid::Operand,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            format!("operand{operand_counter}_value"),
            operand.expression.get_type().to_snapshot(self)?,
        ))
    }
}

pub(in super::super) trait BuiltinMethodsInterface {
    fn encode_memory_block_copy_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_memory_block_split_method(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;

    fn encode_move_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_change_unique_ref_place_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_duplicate_frac_ref_method(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;

    fn encode_write_address_constant_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_copy_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_write_place_constant_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_havoc_owned_non_aliased_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_havoc_memory_block_method_name(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String>;
    fn encode_havoc_memory_block_method(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;
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
    fn encode_havoc_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: vir_mid::Predicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_ghost_havoc_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: vir_mid::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_open_frac_bor_atomic_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_lft_tok_sep_take_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()>;
    fn encode_lft_tok_sep_return_method(&mut self, lft_count: usize) -> SpannedEncodingResult<()>;
    fn encode_newlft_method(&mut self) -> SpannedEncodingResult<()>;
    fn encode_endlft_method(&mut self) -> SpannedEncodingResult<()>;
    fn encode_dead_inclusion_method(&mut self) -> SpannedEncodingResult<()>;
    fn encode_open_close_mut_ref_methods(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_bor_shorten_method(
        &mut self,
        ty_with_lifetime: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> BuiltinMethodsInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_memory_block_copy_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_memory_block_copy_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_memory_block_copy_methods
                .insert(ty_identifier);

            let ty_without_lifetime = ty.clone().erase_lifetimes().erase_const_generics();
            let type_decl = self.encoder.get_type_decl_mid(&ty_without_lifetime)?;
            let mut builder = MemoryBlockCopyMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "memory_copy",
                &ty_without_lifetime,
                &type_decl,
                BuiltinMethodKind::CopyMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_permission_amount_positive_precondition()?;
            builder.add_target_invariant()?;
            builder.add_source_invariant()?;
            builder.add_source_preserved_postcondition()?;
            builder.add_target_is_source_postcondition()?;
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }

    fn encode_write_address_constant_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_write_address_constant_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_write_address_constant_methods
                .insert(ty_identifier);

            self.encode_snapshot_to_bytes_function(ty)?;
            self.encode_memory_block_predicate()?;

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = WriteAddressConstantMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "write_address_constant",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::WriteConstant,
            )?;
            builder.create_parameters()?;
            builder.add_const_parameters_validity_precondition()?;
            let memory_block = builder.create_target_memory_block()?;
            builder.add_precondition(memory_block.clone());
            builder.add_postcondition(memory_block);
            builder.add_target_snapshot_postcondition()?;

            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_move_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_move_place_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_move_place_methods
                .insert(ty_identifier);

            self.encode_compute_address(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();

            let mut builder = MovePlaceMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "move_place",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::MovePlace,
            )?;
            builder.create_parameters()?;
            // FIXME: To generate body for arrays, we would need to generate a
            // loop, which is currently not implemented.
            let has_body = !matches!(
                type_decl,
                vir_mid::TypeDecl::Trusted(_)
                    | vir_mid::TypeDecl::TypeVar(_)
                    | vir_mid::TypeDecl::Array(_)
            );
            let target_memory_block = builder.create_target_memory_block()?;
            builder.add_precondition(target_memory_block);
            let source_owned = builder.create_source_owned()?;
            builder.add_precondition(source_owned);
            let target_owned = builder.create_target_owned()?;
            builder.add_postcondition(target_owned);
            let source_memory_block = builder.create_source_memory_block()?;
            builder.add_postcondition(source_memory_block);
            // builder.add_source_bytes_unchanged_postcondition()?; FIXME – is this needed?
            builder.add_target_validity_postcondition()?;
            if has_body {
                builder.create_body();
                let source_owned = builder.create_source_owned()?;
                builder.add_statement(vir_low::Statement::unfold_no_pos(source_owned));
            }
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Map(_) => {
                    builder.add_memory_block_copy_call()?;
                }
                vir_mid::TypeDecl::Reference(vir_mid::type_decl::Reference {
                    uniqueness, ..
                }) => {
                    builder.add_memory_block_copy_call()?;
                    if uniqueness.is_unique() {
                        builder.change_unique_ref_place()?;
                    } else {
                        builder.duplicate_frac_ref()?;
                    }
                }
                vir_mid::TypeDecl::TypeVar(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::Array(_) => {
                    assert!(
                        !has_body,
                        "move_place of a generic or trusted type has no body"
                    );
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_split_target_memory_block_call()?;
                    for field in &decl.fields {
                        builder.add_move_place_call_for_field(field)?;
                    }
                    builder.add_join_source_memory_block_call()?;
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    builder.add_split_target_memory_block_call()?;
                    for (discriminant_value, variant) in decl.iter_discriminant_variants() {
                        builder.add_move_place_call_for_variant(discriminant_value, variant)?;
                    }
                    if decl.safety.is_enum() {
                        builder.add_move_place_call_for_discriminant(decl)?;
                    }
                    builder.add_join_source_memory_block_call()?;
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            if has_body {
                let target_owned = builder.create_target_owned()?;
                builder.add_statement(vir_low::Statement::fold_no_pos(target_owned));
            }
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }

    fn encode_change_unique_ref_place_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_change_unique_ref_place_method
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_change_unique_ref_place_method
                .insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = ChangeUniqueRefPlaceMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "change_unique_ref_place",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::ChangeUniqueRefPlace,
            )?;
            builder.create_parameters()?;
            builder.add_same_address_precondition()?;
            builder.add_unique_ref_pre_postcondition()?;
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }

    fn encode_duplicate_frac_ref_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_duplicate_frac_ref_method
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_duplicate_frac_ref_method
                .insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = DuplicateFracRefMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "duplicate_frac_ref",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::DuplicateFracRef,
            )?;
            builder.create_parameters()?;
            builder.add_same_address_precondition()?;
            builder.add_frac_ref_pre_postcondition()?;
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }

    fn encode_copy_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_copy_place_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_copy_place_methods
                .insert(ty_identifier);

            self.encode_compute_address(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();

            let mut builder = CopyPlaceMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "copy_place",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::MovePlace,
            )?;
            builder.create_parameters()?;
            // FIXME: To generate body for arrays, we would need to generate a
            // loop, which is currently not implemented.
            let has_body = !matches!(
                type_decl,
                vir_mid::TypeDecl::Trusted(_)
                    | vir_mid::TypeDecl::TypeVar(_)
                    | vir_mid::TypeDecl::Array(_)
            );
            builder.add_permission_amount_positive_precondition()?;
            let target_memory_block = builder.create_target_memory_block()?;
            builder.add_precondition(target_memory_block);
            let source_owned = builder.create_source_owned()?;
            builder.add_precondition(source_owned.clone());
            builder.add_postcondition(source_owned);
            let target_owned = builder.create_target_owned()?;
            builder.add_postcondition(target_owned);
            builder.add_target_validity_postcondition()?;
            if has_body {
                builder.create_body();
                let source_owned = builder.create_source_owned()?;
                builder.add_statement(vir_low::Statement::unfold_no_pos(source_owned));
            }
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Map(_) => {
                    builder.add_memory_block_copy_call()?;
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_split_target_memory_block_call()?;
                    for field in &decl.fields {
                        builder.add_copy_place_call_for_field(field)?;
                    }
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            if has_body {
                let target_owned = builder.create_target_owned()?;
                builder.add_statement(vir_low::Statement::fold_no_pos(target_owned));
                let source_owned = builder.create_source_owned()?;
                builder.add_statement(vir_low::Statement::fold_no_pos(source_owned));
            }
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_write_place_constant_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_write_place_constant_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_write_place_constant_methods
                .insert(ty_identifier);

            self.encode_compute_address(ty)?;

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = WritePlaceConstantMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "write_place_constant",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::WriteConstant,
            )?;
            builder.create_parameters()?;
            // FIXME: To generate body for arrays, we would need to generate a
            // loop, which is currently not implemented.
            let has_body = !matches!(
                type_decl,
                vir_mid::TypeDecl::Trusted(_)
                    | vir_mid::TypeDecl::TypeVar(_)
                    | vir_mid::TypeDecl::Array(_)
            );
            let target_memory_block = builder.create_target_memory_block()?;
            builder.add_precondition(target_memory_block);
            builder.add_source_validity_precondition()?;
            let target_owned = builder.create_target_owned()?;
            builder.add_postcondition(target_owned);
            if has_body {
                builder.create_body();
            }
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Map(_) => {
                    builder.add_write_address_constant_call()?;
                }
                vir_mid::TypeDecl::TypeVar(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::Array(_) => {
                    assert!(
                        !has_body,
                        "write_constant of a generic or trusted type has no body"
                    );
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_split_target_memory_block_call()?;
                    for field in &decl.fields {
                        builder.add_write_constant_call_for_field(field)?;
                    }
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            if has_body {
                let target_owned = builder.create_target_owned()?;
                builder.add_statement(vir_low::Statement::fold_no_pos(target_owned));
            }
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_havoc_owned_non_aliased_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_owned_non_aliased_havoc_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_owned_non_aliased_havoc_methods
                .insert(ty_identifier);
            use vir_low::macros::*;
            let method_name = self.encode_havoc_owned_non_aliased_method_name(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            var_decls! {
                place: Place,
                root_address: Address,
                old_snapshot: {ty.to_snapshot(self)?},
                fresh_snapshot: {ty.to_snapshot(self)?}
            };
            let validity =
                self.encode_snapshot_valid_call_for_type(fresh_snapshot.clone().into(), ty)?;
            let mut parameters = vec![place.clone(), root_address.clone(), old_snapshot.clone()];
            parameters.extend(self.create_lifetime_parameters(&type_decl)?);
            let predicate_in = self.owned_non_aliased_full_vars(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &old_snapshot,
            )?;
            let predicate_out = self.owned_non_aliased_full_vars(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &fresh_snapshot,
            )?;
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::Havoc,
                parameters,
                vec![fresh_snapshot.clone()],
                vec![predicate_in],
                vec![predicate_out, validity],
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_memory_block_split_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_memory_block_split_methods
            .contains(&ty_identifier)
        {
            assert!(
                !ty.is_trusted() && !ty.is_type_var(),
                "Trying to split an abstract type."
            );
            self.builtin_methods_state
                .encoded_memory_block_split_methods
                .insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = MemoryBlockSplitMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "memory_block_split",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::SplitMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_permission_amount_positive_precondition()?;
            builder.add_whole_memory_block_precondition()?;
            match &type_decl {
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_padding_memory_block_postcondition()?;
                    let mut field_to_bytes_equalities = Vec::new();
                    for field in &decl.fields {
                        builder.add_field_memory_block_postcondition(field)?;
                        field_to_bytes_equalities
                            .push(builder.create_field_to_bytes_equality(field)?);
                    }
                    builder
                        .add_fields_to_bytes_equalities_postcondition(field_to_bytes_equalities)?;
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    builder.add_padding_memory_block_postcondition()?;
                    if decl.safety.is_enum() {
                        builder.add_discriminant_postcondition(decl)?;
                    }
                    for (discriminant, variant) in decl.iter_discriminant_variants() {
                        builder.add_variant_memory_block_postcondition(discriminant, variant)?;
                    }
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_memory_block_join_methods
            .contains(&ty_identifier)
        {
            assert!(
                !ty.is_trusted() && !ty.is_type_var(),
                "Trying to join an abstract type."
            );
            self.builtin_methods_state
                .encoded_memory_block_join_methods
                .insert(ty_identifier);

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = MemoryBlockJoinMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "memory_block_join",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::JoinMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_permission_amount_positive_precondition()?;
            builder.add_whole_memory_block_postcondition()?;
            match &type_decl {
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_padding_memory_block_precondition()?;
                    let mut field_to_bytes_equalities = Vec::new();
                    for field in &decl.fields {
                        builder.add_field_memory_block_precondition(field)?;
                        field_to_bytes_equalities
                            .push(builder.create_field_to_bytes_equality(field)?);
                    }
                    builder
                        .add_fields_to_bytes_equalities_postcondition(field_to_bytes_equalities)?;
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    builder.add_padding_memory_block_precondition()?;
                    if decl.safety.is_enum() {
                        builder.add_discriminant_precondition(decl)?;
                    }
                    let mut variant_to_bytes_equalities = Vec::new();
                    for (discriminant, variant) in decl.iter_discriminant_variants() {
                        builder.add_variant_memory_block_precondition(discriminant, variant)?;
                        variant_to_bytes_equalities.push(
                            builder.create_variant_to_bytes_equality(
                                discriminant,
                                variant,
                                decl,
                                decl.safety,
                            )?,
                        );
                    }
                    builder.add_variants_to_bytes_equalities_postcondition(
                        variant_to_bytes_equalities,
                    )?;
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            let method = builder.build();
            self.declare_method(method)?;
        }
        Ok(())
    }
    fn encode_havoc_memory_block_method_name(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!(
            "havoc_memory_block${}${}${}",
            ty.get_identifier(),
            ty.get_lifetimes()
                .into_iter()
                .map(|lifetime| lifetime.to_string())
                .join("$"),
            ty.get_const_arguments()
                .into_iter()
                .map(|arg| arg.to_string())
                .join("$"),
        ))
    }
    fn encode_havoc_memory_block_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let method_name = self.encode_havoc_memory_block_method_name(ty)?;
        if !self
            .builtin_methods_state
            .encoded_memory_block_havoc_methods
            .contains(&method_name)
        {
            self.builtin_methods_state
                .encoded_memory_block_havoc_methods
                .insert(method_name.clone());
            use vir_low::macros::*;
            self.encode_snapshot_to_bytes_function(ty)?;
            let size_of = self.encode_type_size_expression2(ty, ty)?;
            var_decls!(address: Address);
            let predicate = expr! {
                acc(MemoryBlock((address), [size_of]))
            };
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::LowMemoryOperation,
                vec![address],
                Vec::new(),
                vec![predicate.clone()],
                vec![predicate],
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
    // FIXME: This method has to be inlined if the converted type has a resource
    // invariant in it. Otherwise, that resource would be leaked.
    fn encode_into_memory_block_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_into_memory_block_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_into_memory_block_methods
                .insert(ty_identifier);

            self.mark_owned_non_aliased_as_unfolded(ty)?;

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = IntoMemoryBlockMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "into_memory_block",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::SplitMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_const_parameters_validity_precondition()?;
            let predicate = builder.create_owned()?;
            builder.add_precondition(predicate);
            let memory_block = builder.create_target_memory_block()?;
            builder.add_postcondition(memory_block);
            // builder.add_source_bytes_unchanged_postcondition()?; FIXME – is this needed?
            // FIXME: To generate body for arrays, we would need to generate a
            // loop, which is currently not implemented.
            let has_body = !matches!(
                type_decl,
                vir_mid::TypeDecl::Trusted(_)
                    | vir_mid::TypeDecl::TypeVar(_)
                    | vir_mid::TypeDecl::Array(_)
            );
            if has_body {
                builder.create_body();
                let predicate = builder.create_owned()?;
                builder.add_statement(vir_low::Statement::unfold_no_pos(predicate));
            }
            match &type_decl {
                vir_mid::TypeDecl::Bool
                | vir_mid::TypeDecl::Int(_)
                | vir_mid::TypeDecl::Float(_)
                | vir_mid::TypeDecl::Reference(_)
                | vir_mid::TypeDecl::Pointer(_)
                | vir_mid::TypeDecl::Sequence(_)
                | vir_mid::TypeDecl::Map(_) => {
                    // Primitive type. Nothing to do.
                }
                vir_mid::TypeDecl::TypeVar(_)
                | vir_mid::TypeDecl::Trusted(_)
                | vir_mid::TypeDecl::Array(_) => {
                    assert!(
                        !has_body,
                        "write_constant of a generic or trusted type has no body"
                    );
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    for field in &decl.fields {
                        builder.add_into_memory_block_call_for_field(field)?;
                    }
                    builder.add_join_memory_block_call()?;
                }
                vir_mid::TypeDecl::Enum(decl) => {
                    if decl.safety.is_enum() {
                        builder.add_into_memory_block_call_for_discriminant(decl)?;
                    }
                    for (discriminant_value, variant) in decl.iter_discriminant_variants() {
                        builder
                            .add_into_memory_block_call_for_variant(discriminant_value, variant)?;
                    }
                    builder.add_join_memory_block_call()?;
                }
                _ => unimplemented!("{type_decl:?}"),
            }

            let method = builder.build();
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
        let mut arguments = vec![target_place.clone(), target_address.clone()];
        self.encode_rvalue_arguments(&target, &mut arguments, &value)?;
        let target_value_type = target.get_type().to_snapshot(self)?;
        let result_value = self.create_new_temporary_variable(target_value_type)?;
        let assign_statement = vir_low::Statement::method_call(
            method_name,
            arguments,
            vec![result_value.clone().into()],
            position,
        );
        if let vir_mid::Rvalue::Discriminant(value) = value {
            let target_ty = target.get_type();
            let source = {
                let normalized_type = value.place.get_type().normalize_type();
                let type_decl = self.encoder.get_type_decl_mid(&normalized_type)?;
                let decl = type_decl.unwrap_enum();
                let discriminant_field = decl.discriminant_field();
                vir_mid::Expression::field(value.place.clone(), discriminant_field, position)
            };
            let source_place = self.encode_expression_as_place(&source)?;
            let source_root_address = self.extract_root_address(&source)?;
            let source_permission_amount = if let Some(source_permission) = &value.source_permission
            {
                source_permission.to_procedure_snapshot(self)?.into()
            } else {
                vir_low::Expression::full_permission()
            };
            let source_snapshot = source.to_procedure_snapshot(self)?;
            self.encode_copy_place_method(target_ty)?;
            let mut copy_place_statements = vec![self.call_copy_place_method(
                CallContext::Procedure,
                target_ty,
                target_ty,
                position,
                target_place,
                target_address,
                source_place,
                source_root_address,
                source_snapshot.clone(),
                source_permission_amount,
            )?];
            let new_snapshot = self.new_snapshot_variable_version(&target.get_base(), position)?;
            self.encode_snapshot_update_with_new_snapshot(
                &mut copy_place_statements,
                &target,
                source_snapshot,
                position,
                Some(new_snapshot.clone()),
            )?;
            if let Some(conditions) = value.use_field {
                let mut disjuncts = Vec::new();
                for condition in conditions {
                    disjuncts.push(self.lower_block_marker_condition(condition)?);
                }
                let mut else_branch = vec![assign_statement];
                self.encode_snapshot_update_with_new_snapshot(
                    &mut else_branch,
                    &target,
                    result_value.into(),
                    position,
                    Some(new_snapshot),
                )?;
                statements.push(vir_low::Statement::conditional(
                    disjuncts.into_iter().disjoin(),
                    copy_place_statements,
                    else_branch,
                    position,
                ));
            } else {
                // Use field unconditionally.
                statements.extend(copy_place_statements);
            }
        } else {
            statements.push(assign_statement);
            self.encode_snapshot_update(
                statements,
                &target,
                result_value.clone().into(),
                position,
            )?;
            if let vir_mid::Rvalue::Ref(value) = value {
                let snapshot = if value.uniqueness.is_unique() {
                    self.reference_target_final_snapshot(
                        target.get_type(),
                        result_value.into(),
                        position,
                    )?
                } else {
                    self.reference_target_current_snapshot(
                        target.get_type(),
                        result_value.into(),
                        position,
                    )?
                };
                self.encode_snapshot_update(statements, &value.place, snapshot, position)?;
            }
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
        self.encode_consume_operand_method(&method_name, &operand, position)?;
        let mut arguments = Vec::new();
        self.encode_operand_arguments(&mut arguments, &operand, true)?;
        statements.push(vir_low::Statement::method_call(
            method_name,
            arguments,
            Vec::new(),
            position,
        ));
        Ok(())
    }
    fn encode_havoc_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        predicate: vir_mid::Predicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        match predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                self.encode_havoc_owned_non_aliased_method(ty)?;
                self.mark_owned_non_aliased_as_unfolded(ty)?;
                let place = self.encode_expression_as_place(&predicate.place)?;
                let address = self.extract_root_address(&predicate.place)?;
                let old_snapshot = predicate.place.to_procedure_snapshot(self)?;
                let snapshot_type = ty.to_snapshot(self)?;
                let fresh_snapshot = self.create_new_temporary_variable(snapshot_type)?;
                let method_name = self.encode_havoc_owned_non_aliased_method_name(ty)?;
                let mut arguments = vec![place, address, old_snapshot];
                arguments.extend(self.create_lifetime_arguments(CallContext::Procedure, ty)?);
                statements.push(vir_low::Statement::method_call(
                    method_name,
                    arguments,
                    vec![fresh_snapshot.clone().into()],
                    position,
                ));
                self.encode_snapshot_update(
                    statements,
                    &predicate.place,
                    fresh_snapshot.into(),
                    position,
                )?;
            }
            vir_mid::Predicate::MemoryBlockStack(predicate) => {
                let ty = predicate.place.get_type();
                self.encode_havoc_memory_block_method(ty)?;
                let method_name = self.encode_havoc_memory_block_method_name(ty)?;
                let address = self.encode_expression_as_place_address(&predicate.place)?;
                let statement =
                    vir_low::Statement::method_call_no_pos(method_name, vec![address], Vec::new());
                statements.push(statement.set_default_position(position));
            }
            _ => unimplemented!(),
        }
        Ok(())
    }

    fn encode_ghost_havoc_method_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        variable: vir_mid::VariableDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let ty = variable.ty.to_snapshot(self)?;
        let fresh_value = self.create_new_temporary_variable(ty)?;
        let variable_expr = vir_mid::Expression::local(variable, position);
        self.encode_snapshot_update(statements, &variable_expr, fresh_value.into(), position)
    }

    fn encode_open_frac_bor_atomic_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_open_frac_bor_atomic_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_open_frac_bor_atomic_methods
                .insert(ty_identifier);
            self.encode_lifetime_token_predicate()?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            use vir_low::macros::*;
            var_decls! {
                lifetime: Lifetime,
                lifetime_perm: Perm,
                owned_perm: Perm,
                place: Place,
                root_address: Address,
                current_snapshot: {ty.to_snapshot(self)?}
            };
            let lifetime_access = expr! { acc(LifetimeToken(lifetime), lifetime_perm) };
            let frac_ref_access = self.frac_ref_full_vars(
                CallContext::BuiltinMethod,
                ty,
                ty,
                &place,
                &root_address,
                &current_snapshot,
                &lifetime,
            )?;
            let owned_access = self.owned_non_aliased(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                place.clone().into(),
                root_address.clone().into(),
                current_snapshot.clone().into(),
                Some(owned_perm.clone().into()),
            )?;
            let method = vir_low::MethodDecl::new(
                self.encode_open_frac_bor_atomic_method_name(ty)?,
                vir_low::MethodKind::MirOperation,
                vec![
                    lifetime,
                    lifetime_perm.clone(),
                    place,
                    root_address,
                    current_snapshot,
                ],
                vec![owned_perm.clone()],
                vec![
                    expr! {
                        [vir_low::Expression::no_permission()] < lifetime_perm
                    },
                    lifetime_access.clone(),
                    frac_ref_access.clone(),
                ],
                vec![
                    expr! {
                        owned_perm < [vir_low::Expression::full_permission()]
                    },
                    expr! {
                        [vir_low::Expression::no_permission()] < owned_perm
                    },
                    owned_access.clone(),
                    vir_low::Expression::magic_wand_no_pos(
                        owned_access,
                        expr! { [lifetime_access] && [frac_ref_access] },
                    ),
                ],
                None,
            );
            self.declare_method(method)?;
        }
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
                pres.push(self.encode_lifetime_token(lifetime.clone(), rd_perm.clone().into())?);
            }
            parameters.push(rd_perm.clone());

            // Postconditions
            var_decls!(lft: Lifetime);
            let lifetimes_expr = self.create_lifetime_expressions(lft_count)?;
            let lifetime_set_type = self.lifetime_set_type()?;
            let lifetime_set = vir_low::Expression::container_op_no_pos(
                vir_low::ContainerOpKind::SetConstructor,
                lifetime_set_type,
                lifetimes_expr,
            );
            let intersect = self.create_domain_func_app(
                "Lifetime",
                "intersect",
                vec![lifetime_set],
                ty!(Lifetime),
                Default::default(),
            )?;
            let posts = vec![
                self.encode_lifetime_token(lft.clone(), rd_perm.into())?,
                vir_low::Expression::binary_op_no_pos(
                    vir_low::BinaryOpKind::EqCmp,
                    lft.clone().into(),
                    intersect,
                ),
            ];

            // Create Method
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::MirOperation,
                parameters,
                vec![lft],
                pres,
                posts,
                None,
            );
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
            use vir_low::macros::*;

            let method_name = self.encode_lft_tok_sep_return_method_name(lft_count)?;
            var_decls!(lft: Lifetime); // target
            var_decls!(rd_perm: Perm);
            let lifetimes_var: Vec<vir_low::VariableDecl> =
                self.create_lifetime_var_decls(lft_count)?;
            let lifetime_set_type = self.lifetime_set_type()?;
            let lifetimes_expr = self.create_lifetime_expressions(lft_count)?;
            let lifetime_set = vir_low::Expression::container_op_no_pos(
                vir_low::ContainerOpKind::SetConstructor,
                lifetime_set_type,
                lifetimes_expr,
            );
            let intersect = self.create_domain_func_app(
                "Lifetime",
                "intersect",
                vec![lifetime_set],
                ty!(Lifetime),
                Default::default(),
            )?;

            // Parameters
            let mut parameters = vec![lft.clone()];
            parameters.append(lifetimes_var.clone().as_mut());
            parameters.push(rd_perm.clone());

            // Preconditions
            let pres = vec![
                expr! {
                    [vir_low::Expression::no_permission()] < rd_perm
                },
                self.encode_lifetime_token(lft.clone(), rd_perm.clone().into())?,
                vir_low::Expression::binary_op_no_pos(
                    vir_low::BinaryOpKind::EqCmp,
                    lft.into(),
                    intersect,
                ),
            ];

            // Postconditions
            let posts: Vec<vir_low::Expression> = lifetimes_var
                .into_iter()
                .map(|lifetime| self.encode_lifetime_token(lifetime, rd_perm.clone().into()))
                .collect::<Result<_, _>>()?;

            // Create Method
            let method = vir_low::MethodDecl::new(
                method_name,
                vir_low::MethodKind::MirOperation,
                parameters,
                vec![],
                pres,
                posts,
                None,
            );
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
                vir_low::MethodKind::MirOperation,
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
    fn encode_dead_inclusion_method(&mut self) -> SpannedEncodingResult<()> {
        if !self.builtin_methods_state.encoded_dead_inclusion_method {
            self.builtin_methods_state.encoded_dead_inclusion_method = true;
            self.encode_lifetime_token_predicate()?;
            self.encode_lifetime_included()?;
            use vir_low::macros::*;
            var_decls! {
                lft_1: Lifetime,
                lft_2: Lifetime
            }
            let included = ty!(Bool);
            let pres = vec![
                expr! { acc(DeadLifetimeToken(lft_2))},
                expr! { Lifetime::included( lft_1, lft_2 ) },
            ];
            let posts = vec![
                expr! { acc(DeadLifetimeToken(lft_1))},
                expr! { acc(DeadLifetimeToken(lft_2))},
            ];
            let method = vir_low::MethodDecl::new(
                "dead_inclusion",
                vir_low::MethodKind::MirOperation,
                vec![lft_1, lft_2],
                vec![],
                pres,
                posts,
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
                vir_low::MethodKind::MirOperation,
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
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_open_close_mut_ref_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_open_close_mut_ref_methods
                .insert(ty_identifier);
            self.encode_lifetime_token_predicate()?;
            use vir_low::macros::*;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;

            var_decls! {
                lifetime: Lifetime,
                lifetime_perm: Perm,
                place: Place,
                root_address: Address,
                current_snapshot: {ty.to_snapshot(self)?},
                final_snapshot: {ty.to_snapshot(self)?}
            };
            let owned_predicate = self.owned_non_aliased_full_vars(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &current_snapshot,
            )?;
            let unique_ref_predicate = self.unique_ref_full_vars(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &current_snapshot,
                &final_snapshot,
                &lifetime,
            )?;
            let open_method = vir_low::MethodDecl::new(
                method_name! { open_mut_ref<ty> },
                vir_low::MethodKind::MirOperation,
                vec![
                    lifetime.clone(),
                    lifetime_perm.clone(),
                    place.clone(),
                    root_address.clone(),
                    current_snapshot.clone(),
                    final_snapshot.clone(),
                ],
                Vec::new(),
                vec![
                    expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                    expr! { acc(LifetimeToken(lifetime), lifetime_perm) },
                    unique_ref_predicate.clone(),
                ],
                vec![
                    owned_predicate.clone(),
                    // CloseMutRef predicate corresponds to the following
                    // viewshift:
                    // ```
                    // (acc(OwnedNonAliased<ty>(
                    //     [deref_place],
                    //     [address_snapshot],
                    //     ?current_snapshot
                    // ))) --* (
                    //     (acc(LifetimeToken(lifetime), lifetime_perm)) &&
                    //     (acc(UniqueRef<ty>(
                    //         lifetime,
                    //         [deref_place],
                    //         [address_snapshot],
                    //         current_snapshot,
                    //         [final_snapshot]
                    //     )))
                    // )
                    // ```
                    expr! { acc(CloseMutRef<ty>(
                        lifetime,
                        lifetime_perm,
                        place,
                        root_address,
                        final_snapshot
                    ))},
                ],
                None,
            );
            self.declare_method(open_method)?;

            {
                let close_mut_ref_predicate = vir_low::PredicateDecl::new(
                    predicate_name! { CloseMutRef<ty> },
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        place.clone(),
                        root_address.clone(),
                        final_snapshot.clone(),
                    ],
                    None,
                );
                self.declare_predicate(close_mut_ref_predicate)?;
                // Apply the viewshift encoded in the `CloseMutRef` predicate.
                let close_method = vir_low::MethodDecl::new(
                    method_name! { close_mut_ref<ty> },
                    vir_low::MethodKind::MirOperation,
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        place.clone(),
                        root_address.clone(),
                        current_snapshot.clone(),
                        final_snapshot.clone(),
                    ],
                    Vec::new(),
                    vec![
                        expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                        expr! { acc(CloseMutRef<ty>(
                            lifetime,
                            lifetime_perm,
                            place,
                            root_address,
                            final_snapshot
                        ))},
                        owned_predicate,
                    ],
                    vec![
                        expr! { acc(LifetimeToken(lifetime), lifetime_perm) },
                        unique_ref_predicate,
                    ],
                    None,
                );
                self.declare_method(close_method)?;
            }
        }
        Ok(())
    }
    fn encode_bor_shorten_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_bor_shorten_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_bor_shorten_methods
                .insert(ty_identifier);
            use vir_low::macros::*;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let reference_type = type_decl.unwrap_reference();
            let target_type = &reference_type.target_type;
            let included = ty!(Bool);
            var_decls! {
                lft: Lifetime,
                old_lft: Lifetime,
                lifetime_perm: Perm,
                place: Place,
                root_address: Address,
                current_snapshot: {target_type.to_snapshot(self)?},
                final_snapshot: {target_type.to_snapshot(self)?}
            }
            let mut parameters = vec![
                lft.clone(),
                old_lft.clone(),
                lifetime_perm.clone(),
                place.clone(),
                root_address.clone(),
                current_snapshot.clone(),
            ];
            if reference_type.uniqueness.is_unique() {
                parameters.push(final_snapshot.clone());
            }
            let mut pres = vec![
                expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                expr! { lifetime_perm < [vir_low::Expression::full_permission()] },
                expr! { Lifetime::included([lft.clone().into()], [old_lft.clone().into()])},
                expr! { acc(LifetimeToken(lft), lifetime_perm)},
            ];
            let mut posts = vec![expr! { acc(LifetimeToken(lft), lifetime_perm)}];
            if reference_type.uniqueness.is_unique() {
                pres.push(self.unique_ref_full_vars(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &root_address,
                    &current_snapshot,
                    &final_snapshot,
                    &old_lft,
                )?);
                posts.push(self.unique_ref_full_vars(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &root_address,
                    &current_snapshot,
                    &final_snapshot,
                    &lft,
                )?);
            } else {
                pres.push(self.frac_ref_full_vars(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &root_address,
                    &current_snapshot,
                    &old_lft,
                )?);
                posts.push(self.frac_ref_full_vars(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &root_address,
                    &current_snapshot,
                    &lft,
                )?);
            }
            parameters.extend(self.create_lifetime_parameters(target_type)?);
            let method = vir_low::MethodDecl::new(
                method_name! { bor_shorten<ty> },
                vir_low::MethodKind::MirOperation,
                parameters,
                vec![],
                pres,
                posts,
                None,
            );
            self.declare_method(method)?;
        }
        Ok(())
    }
}
