use super::{
    builders::{
        ChangeUniqueRefPlaceMethodBuilder, DuplicateFracRefMethodBuilder,
        MemoryBlockCopyMethodBuilder, RestoreRawBorrowedMethodBuilder,
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
            MemoryBlockJoinMethodBuilder, MemoryBlockRangeJoinMethodBuilder,
            MemoryBlockRangeSplitMethodBuilder, MemoryBlockSplitMethodBuilder,
            MovePlaceMethodBuilder, WriteAddressConstantMethodBuilder,
            WritePlaceConstantMethodBuilder,
        },
        compute_address::ComputeAddressInterface,
        const_generics::ConstGenericsInterface,
        errors::ErrorsInterface,
        footprint::FootprintInterface,
        lifetimes::LifetimesInterface,
        lowerer::{
            DomainsLowererInterface, Lowerer, MethodsLowererInterface, PredicatesLowererInterface,
            VariablesLowererInterface,
        },
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{
            OwnedNonAliasedSnapCallBuilder, OwnedNonAliasedUseBuilder, PredicatesAliasingInterface,
            PredicatesMemoryBlockInterface, PredicatesOwnedInterface, RestorationInterface,
        },
        references::ReferencesInterface,
        snapshots::{
            AssertionToSnapshotConstructor, BuiltinFunctionsInterface, IntoBuiltinMethodSnapshot,
            IntoProcedureSnapshot, IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer,
            PlaceToSnapshot, PredicateKind, SelfFramingAssertionToSnapshot, SnapshotBytesInterface,
            SnapshotValidityInterface, SnapshotValuesInterface, SnapshotVariablesInterface,
        },
        triggers::TriggersInterface,
        type_layouts::TypeLayoutsInterface,
        viewshifts::ViewShiftsInterface,
    },
    mir::errors::ErrorInterface,
};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::{
    common::{
        builtin_constants::LIFETIME_DOMAIN_NAME,
        check_mode::CheckMode,
        expression::{
            BinaryOperationHelpers, ExpressionIterator, QuantifierHelpers, UnaryOperationHelpers,
        },
        identifier::WithIdentifier,
        position::Positioned,
    },
    low::{self as vir_low, macros::method_name},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes, ty::Typed},
    },
};

// FIXME: Move this to some proper place. It is shared with the snap function
// encoder.

#[derive(Default)]
pub(in super::super) struct BuiltinMethodsState {
    encoded_write_place_constant_methods: FxHashSet<String>,
    encoded_move_place_methods: FxHashSet<String>,
    encoded_copy_place_methods: FxHashSet<String>,
    encoded_change_unique_ref_place_method: FxHashSet<String>,
    encoded_duplicate_frac_ref_method: FxHashSet<String>,
    encoded_write_address_constant_methods: FxHashSet<String>,
    encoded_owned_non_aliased_havoc_methods: FxHashSet<String>,
    encoded_unique_ref_havoc_methods: FxHashSet<String>,
    encoded_memory_block_copy_methods: FxHashSet<String>,
    encoded_memory_block_split_methods: FxHashSet<String>,
    encoded_memory_block_range_split_methods: FxHashSet<String>,
    encoded_memory_block_join_methods: FxHashSet<String>,
    encoded_memory_block_range_join_methods: FxHashSet<String>,
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
    encoded_restore_raw_borrowed_methods: FxHashSet<String>,
    encoded_bor_shorten_methods: FxHashSet<String>,
    encoded_stashed_owned_aliased_predicates: FxHashSet<String>,
    encoded_assign_method_names: FxHashMap<String, String>,
    reborrow_target_variables:
        FxHashMap<vir_mid::ty::LifetimeConst, (vir_low::VariableDecl, vir_mid::Type)>,
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
        &mut self,
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
    fn encode_havoc_unique_ref_method_name(
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
                arguments.push(self.encode_expression_as_place(&value.deref_place)?);
                // arguments.push(self.extract_root_address(&value.deref_place)?);
                arguments.push(self.encode_expression_as_place_address(&value.deref_place)?);
                // self.encode_place_arguments(arguments, &value.deref_place, false)?;
                // if self.check_mode.unwrap() == CheckMode::PurificationFunctional {
                //     arguments.push(value.deref_place.to_procedure_snapshot(self)?);
                // } else {
                let place = self.encode_expression_as_place(&value.deref_place)?;
                // let root_address = self.extract_root_address(&value.deref_place)?;
                let address = self.encode_expression_as_place_address(&value.deref_place)?;
                let ty = value.deref_place.get_type();
                let TODO_target_slice_len = None;
                match value
                    .deref_place
                    .get_deref_uniqueness()
                    .unwrap_or(value.uniqueness)
                {
                    vir_mid::ty::Uniqueness::Unique => {
                        let snapshot_current = self.unique_ref_snap(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            address,
                            deref_lifetime.clone().into(),
                            TODO_target_slice_len,
                            false,
                            value.deref_place.position(),
                        )?;
                        arguments.push(snapshot_current);
                        let mut place_encoder =
                            PlaceToSnapshot::for_place(PredicateKind::UniqueRef {
                                lifetime: deref_lifetime.clone().into(),
                                is_final: true,
                            });
                        let snapshot_final =
                            place_encoder.expression_to_snapshot(self, &value.deref_place, true)?;
                        // let snapshot_final =
                        //     value.deref_place.to_procedure_final_snapshot(self)?;
                        arguments.push(snapshot_final);
                    }
                    vir_mid::ty::Uniqueness::Shared => {
                        let snapshot_current = self.frac_ref_snap(
                            CallContext::Procedure,
                            ty,
                            ty,
                            place,
                            address,
                            deref_lifetime.clone().into(),
                            TODO_target_slice_len,
                            value.deref_place.position(),
                        )?;
                        arguments.push(snapshot_current);
                    }
                }
                // }
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
            vir_mid::Rvalue::Cast(value) => {
                self.encode_operand_arguments(arguments, &value.operand, true)?;
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
                if self.use_heap_variable()? && aggr_value.ty.is_struct() {
                    let heap = self.heap_variable_version_at_label(&None)?;
                    arguments.push(heap.into());
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
        arguments.push(self.encode_expression_as_place_address(place)?);
        // arguments.push(self.extract_root_address(place)?);
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
        // arguments.push(self.extract_root_address(expression)?);
        arguments.push(self.encode_expression_as_place_address(expression)?);
        let mut place_encoder = PlaceToSnapshot::for_place(PredicateKind::Owned);
        let snapshot = place_encoder.expression_to_snapshot(self, expression, false)?;
        arguments.push(snapshot);
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
        &mut self,
        ty: &vir_mid::Type,
        value: &vir_mid::Rvalue,
    ) -> SpannedEncodingResult<String> {
        let full_name = format!(
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
        );
        if let Some(short_name) = self
            .builtin_methods_state
            .encoded_assign_method_names
            .get(&full_name)
        {
            Ok(short_name.clone())
        } else {
            let short_name = format!(
                "assign${}",
                self.builtin_methods_state.encoded_assign_method_names.len()
            );
            self.builtin_methods_state
                .encoded_assign_method_names
                .insert(full_name, short_name.clone());
            Ok(short_name)
        }
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
    fn encode_havoc_unique_ref_method_name(
        &self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("havoc_unique_ref${}", ty.get_identifier()))
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
            self.mark_owned_predicate_as_unfolded(ty)?;
            let span = self.encoder.get_type_definition_span_mid(ty)?;
            let position = self.register_error(
                span,
                ErrorCtxt::UnexpectedBuiltinMethod(BuiltinMethodKind::MovePlace),
            );
            use vir_low::macros::*;
            // let compute_address = ty!(Address);
            let size_of = self.encode_type_size_expression2(ty, ty)?;
            var_decls! {
                target_place: PlaceOption,
                target_address: Address
            };
            let mut parameters = vec![target_place.clone(), target_address.clone()];
            var_decls! { result_value: {ty.to_snapshot(self)?} };
            let mut pres = vec![
                // expr! { acc(MemoryBlock((ComputeAddress::compute_address(target_place, target_address)), [size_of])) },
                expr! { acc(MemoryBlock(target_address, [size_of])) },
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
                    let predicate = self.owned_non_aliased_full_vars_with_snapshot(
                        CallContext::BuiltinMethod,
                        ty,
                        ty,
                        &target_place,
                        &target_address,
                        &result_value,
                        position,
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
                    operand_place: PlaceOption,
                    operand_address: Address,
                    operand_value: { ty.to_snapshot(self)? }
                };
                let non_aliased_predicate = self.owned_non_aliased_full_vars_with_snapshot(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    &operand_place,
                    &operand_address,
                    &operand_value,
                    position,
                )?;
                pres.push(non_aliased_predicate);
                let aliased_predicate = self.owned_aliased(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    operand_address.clone().into(),
                    None,
                    position,
                )?;
                let aliased_predicate_snapshot = self.owned_aliased_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    operand_address.clone().into(),
                    position,
                )?;
                let restore_raw_borrowed = self.restore_raw_borrowed(
                    ty,
                    operand_place.clone().into(),
                    operand_address.clone().into(),
                )?;
                posts.push(aliased_predicate);
                posts.push(restore_raw_borrowed);
                posts.push(expr! { [aliased_predicate_snapshot] == operand_value });
                parameters.push(operand_place);
                parameters.push(operand_address.clone());
                parameters.push(operand_value);
                self.construct_constant_snapshot(
                    result_type,
                    operand_address.clone().into(),
                    position,
                )?
            }
            vir_mid::Rvalue::Len(_value) => {
                var_decls! { length: {self.size_type()?} };
                parameters.push(length.clone());
                length.into()
            }
            vir_mid::Rvalue::Cast(value) => {
                let source_type = value.operand.expression.get_type();
                let operand_value = self.encode_assign_operand(
                    parameters,
                    pres,
                    posts,
                    1,
                    &value.operand,
                    position,
                    true,
                )?;
                match (&value.ty, source_type) {
                    (vir_mid::Type::Pointer(_), vir_mid::Type::Pointer(_)) => {
                        let address =
                            self.pointer_address(source_type, operand_value.into(), position)?;
                        self.construct_constant_snapshot(result_type, address, position)?
                    }
                    (vir_mid::Type::Int(target_int), vir_mid::Type::Int(_source_int)) => {
                        let number = self.obtain_constant_value(
                            source_type,
                            operand_value.into(),
                            position,
                        )?;
                        let (lower_bound, upper_bound) = match target_int {
                            vir_mid::ty::Int::U8 => (u8::MIN.into(), u8::MAX.into()),
                            vir_mid::ty::Int::U16 => (u16::MIN.into(), u16::MAX.into()),
                            vir_mid::ty::Int::U32 => (u32::MIN.into(), u32::MAX.into()),
                            vir_mid::ty::Int::U64 => (u64::MIN.into(), u64::MAX.into()),
                            vir_mid::ty::Int::U128 => (u128::MIN.into(), u128::MAX.into()),
                            vir_mid::ty::Int::Usize => (usize::MIN.into(), usize::MAX.into()),
                            vir_mid::ty::Int::I8 => (i8::MIN.into(), i8::MAX.into()),
                            vir_mid::ty::Int::I16 => (i16::MIN.into(), i16::MAX.into()),
                            vir_mid::ty::Int::I32 => (i32::MIN.into(), i32::MAX.into()),
                            vir_mid::ty::Int::I64 => (i64::MIN.into(), i64::MAX.into()),
                            vir_mid::ty::Int::I128 => (i128::MIN.into(), i128::MAX.into()),
                            vir_mid::ty::Int::Isize => (isize::MIN.into(), isize::MAX.into()),
                            _ => unimplemented!("{target_int}"),
                        };
                        pres.push(expr! { [lower_bound] <= [number.clone()] }); // FIXME: use the MIN value of the target platform.
                        pres.push(expr! { [number.clone()] <= [upper_bound] }); // FIXME: use the MAX value of the target platform.
                        self.construct_constant_snapshot(result_type, number, position)?
                    }
                    // (
                    //     vir_mid::Type::Int(vir_mid::ty::Int::Isize),
                    //     vir_mid::Type::Int(vir_mid::ty::Int::Usize),
                    // ) => {
                    //     let number = self.obtain_constant_value(
                    //         source_type,
                    //         operand_value.into(),
                    //         position,
                    //     )?;
                    //     pres.push(expr! { [number.clone()] <= [isize::MAX.into()] }); // FIXME: use the MAX value of the target.
                    //     self.construct_constant_snapshot(result_type, number, position)?
                    // }
                    (t, s) => unimplemented!("({t}) {s}"),
                }
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
                    operand_place: PlaceOption,
                    operand_address: Address,
                    operand_permission: Perm,
                    operand_value: { ty.to_snapshot(self)? }
                };
                let predicate = self.owned_non_aliased_with_snapshot(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    operand_place.clone().into(),
                    operand_address.clone().into(),
                    operand_value.clone().into(),
                    Some(operand_permission.clone().into()),
                    position,
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
                        let decl = self.encoder.get_type_decl_mid(&value.ty)?.unwrap_struct();
                        if let Some(invariant) = decl.structural_invariant {
                            assert_eq!(arguments.len(), decl.fields.len());
                            // Assert the invariant for the struct in the precondition.
                            let mut invariant_encoder =
                                SelfFramingAssertionToSnapshot::for_assign_precondition(
                                    arguments.clone(),
                                    decl.fields.clone(),
                                );
                            for assertion in &invariant {
                                let encoded_assertion = invariant_encoder
                                    .expression_to_snapshot(self, assertion, true)?;
                                pres.push(encoded_assertion);
                            }
                            // Create the snapshot constructor.
                            let deref_fields =
                                self.structural_invariant_to_deref_fields(&invariant)?;
                            let mut constructor_encoder =
                                AssertionToSnapshotConstructor::for_assign_aggregate_postcondition(
                                    result_type,
                                    arguments,
                                    decl.fields,
                                    deref_fields,
                                    position,
                                );
                            let invariant_expression = invariant.into_iter().conjoin();
                            let permission_expression =
                                invariant_expression.convert_into_permission_expression();
                            constructor_encoder
                                .expression_to_snapshot_constructor(self, &permission_expression)?
                        } else {
                            self.construct_struct_snapshot(&value.ty, arguments, position)?
                        }
                    }
                    vir_mid::Type::Array(value_ty) => vir_low::Expression::container_op(
                        vir_low::ContainerOpKind::SeqConstructor,
                        vir_low::Type::seq(value_ty.element_type.to_snapshot(self)?),
                        arguments,
                        position,
                    ),
                    ty => unimplemented!("{}", ty),
                };
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
            target_place: PlaceOption,
            target_address: Address
        };
        // let compute_address = ty!(Address);
        let type_decl = self.encoder.get_type_decl_mid(ty)?.unwrap_struct();
        let (operation_result_field, flag_field) = {
            let mut iter = type_decl.fields.iter();
            (iter.next().unwrap(), iter.next().unwrap())
        };
        let flag_place = self.encode_field_place(ty, flag_field, target_place.into(), position)?;
        let flag_address =
            self.encode_field_address(ty, flag_field, target_address.clone().into(), position)?;
        let flag_value = self.obtain_struct_field_snapshot(
            ty,
            flag_field,
            result_value.clone().into(),
            position,
        )?;
        let result_address: vir_low::Expression = target_address.into();
        // expr! { (ComputeAddress::compute_address(target_place, target_address)) };
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
        posts.push(self.owned_non_aliased_with_snapshot(
            CallContext::BuiltinMethod,
            flag_type,
            flag_type,
            flag_place,
            flag_address,
            flag_value.clone(),
            None,
            position,
        )?);
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
        {
            // We verify absence of overflows in all modes because the
            // panic/non-panic behaviour depends on the compiler flags.
            pres.push(validity);
            posts.push(expr! { [operation_result_value.clone()] == [operation_result] });
            // let operation_result_value_condition = expr! {
            //     [validity] ==> ([operation_result_value.clone()] == [operation_result])
            // };
            // posts.push(operation_result_value_condition);
        }
        let flag_value_condition = expr! {
            [flag_value] == [flag_result]
        };
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
        let operand_uniqueness = if let Some(uniqueness) = value.deref_place.get_deref_uniqueness()
        {
            uniqueness
        } else {
            // Reborrowing via a raw pointer. Just assume that its uniqueness matches the target.
            reference_type.uniqueness
        };
        let is_last_deref_pointer = value
            .deref_place
            .get_last_dereference()
            .unwrap()
            .base
            .get_type()
            .is_pointer();
        let ty = value.deref_place.get_type();
        var_decls! {
            target_place: PlaceOption,
            target_address: Address,
            operand_place: PlaceOption,
            operand_address: Address,
            operand_snapshot_current: { ty.to_snapshot(self)? },
            operand_snapshot_final: { ty.to_snapshot(self)? }, // use only for unique references
            lifetime_perm: Perm
        };
        let new_borrow_lifetime = value.new_borrow_lifetime.to_pure_snapshot(self)?;
        let deref_lifetime = value.deref_lifetime.to_pure_snapshot(self)?;
        let lifetime_token =
            self.encode_lifetime_token(new_borrow_lifetime.clone(), lifetime_perm.clone().into())?;
        let deref_predicate = if operand_uniqueness.is_unique() {
            self.unique_ref_full_vars_with_current_snapshot(
                CallContext::BuiltinMethod,
                ty,
                ty,
                &operand_place,
                &operand_address,
                &operand_snapshot_current,
                &deref_lifetime,
                None,
                position,
            )?
        } else {
            self.frac_ref_full_vars_with_current_snapshot(
                CallContext::BuiltinMethod,
                ty,
                ty,
                &operand_place,
                &operand_address,
                &operand_snapshot_current,
                &deref_lifetime,
                None,
                position,
            )?
        };
        let valid_result =
            self.encode_snapshot_valid_call_for_type(result_value.clone().into(), result_type)?;
        let new_reference_predicate = {
            self.mark_owned_predicate_as_unfolded(result_type)?;
            let mut builder = OwnedNonAliasedUseBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.clone().into(),
                target_address.clone().into(),
                position,
            )?;
            // builder.add_snapshot_argument(result_value.clone().into())?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            let predicate = builder.build()?;
            let mut builder = OwnedNonAliasedSnapCallBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.into(),
                target_address.into(),
                position,
            )?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            let snapshot = builder.build()?;
            expr! { [predicate] && (result_value == [snapshot]) }
        };
        let restoration = {
            // if operand_uniqueness.is_unique() && reference_type.uniqueness.is_unique() {
            if operand_uniqueness.is_unique() {
                if is_last_deref_pointer {
                    // We currently cannot allow restoring reborrowed raw
                    // pointers (it would be unsound) because we resolve
                    // inheritance immediately (see the comment below).
                    true.into()
                } else {
                    let final_snapshot = match reference_type.uniqueness {
                        vir_mid::ty::Uniqueness::Unique => self.reference_target_final_snapshot(
                            result_type,
                            result_value.clone().into(),
                            position,
                        )?,
                        vir_mid::ty::Uniqueness::Shared => {
                            // let reference_type = value
                            //     .deref_place
                            //     .get_last_dereferenced_reference()
                            //     .unwrap()
                            //     .get_type();
                            self.reference_target_current_snapshot(
                                result_type,
                                // reference_type,
                                result_value.clone().into(),
                                position,
                            )?
                        }
                    };
                    let deref_predicate = self.unique_ref_with_current_snapshot(
                        CallContext::BuiltinMethod,
                        ty,
                        ty,
                        operand_place.clone().into(),
                        operand_address.clone().into(),
                        final_snapshot.clone(),
                        deref_lifetime.clone().into(),
                        None,
                        None,
                        position,
                    )?;
                    let validity =
                        self.encode_snapshot_valid_call_for_type(final_snapshot.clone(), ty)?;
                    let mut arguments = vec![
                        new_borrow_lifetime.clone().into(),
                        operand_place.clone().into(),
                        operand_address.clone().into(),
                        // operand_snapshot_current.clone().into(),
                        final_snapshot,
                        deref_lifetime.clone().into(),
                    ];
                    arguments
                        .extend(self.create_lifetime_arguments(CallContext::BuiltinMethod, ty)?);
                    arguments.extend(self.create_const_arguments(CallContext::BuiltinMethod, ty)?);
                    self.encode_view_shift_return(
                        &format!("end$reborrow${}", ty.get_identifier()),
                        arguments,
                        vec![expr! { acc(DeadLifetimeToken(new_borrow_lifetime)) }],
                        vec![
                            deref_predicate,
                            validity,
                            // DeadLifetimeToken is duplicable and does not get consumed.
                            expr! { acc(DeadLifetimeToken(new_borrow_lifetime)) },
                        ],
                        vir_low::PredicateKind::EndBorrowViewShift,
                        position,
                    )?
                }
            } else {
                deref_predicate.clone()
            }
        };
        let reference_target_address =
            self.reference_address(result_type, result_value.clone().into(), position)?;
        posts.push(expr! {
            operand_address == [reference_target_address]
        });
        let reference_target_current_snapshot = self.reference_target_current_snapshot(
            result_type,
            result_value.clone().into(),
            position,
        )?;
        posts.push(expr! {
            operand_snapshot_current == [reference_target_current_snapshot]
        });
        if operand_uniqueness.is_unique()
            && reference_type.uniqueness.is_unique()
            && is_last_deref_pointer
        {
            let reference_target_final_snapshot = self.reference_target_final_snapshot(
                result_type,
                result_value.clone().into(),
                position,
            )?;
            // This is sound because we do not generate the inheritance for
            // reborrows of raw pointers. In other words, we resolve the
            // reborrow immediatelly after it is created by destroying the
            // inheritance. This covers most of our use cases. A proper
            // solution would be to make the fold-unfold algorithm to emit
            // statements that explicitly resolve inheritance once it is
            // clear that it will not be used and give an annotation that
            // allows the user to do the same in unsafe code.
            posts.push(expr! {
                operand_snapshot_final == [reference_target_final_snapshot]
            });
        }
        // if operand_uniqueness.is_unique() {
        //     if reference_type.uniqueness.is_unique() {
        //         // We now generate inharitance, so the following would be unsound:
        //         // let reference_target_final_snapshot = self.reference_target_final_snapshot(
        //         //     result_type,
        //         //     result_value.clone().into(),
        //         //     position,
        //         // )?;
        //         // // This is sound because we do not generate the inheritance for
        //         // // reborrows of unique references. In other words, we resolve the
        //         // // reborrow immediatelly after it is created by destroying the
        //         // // inheritance. This covers most of our use cases. A proper solution
        //         // // would be to make the fold-unfold algorithm to emit statements
        //         // // that explicitly resolve inheritance once it is clear that it will
        //         // // not be used and give an annotation that allows the user to do the
        //         // // same in unsafe code.
        //         // posts.push(expr! {
        //         //     operand_snapshot_final == [reference_target_final_snapshot]
        //         // });
        //     } else {
        //         // The snapshot is guaranteed not to change.
        //         posts.push(expr! {
        //             operand_snapshot_final == operand_snapshot_current
        //         });
        //     }
        // }
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
        parameters.push(operand_address);
        parameters.push(operand_snapshot_current);
        if operand_uniqueness.is_unique() {
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
            target_place: PlaceOption,
            target_address: Address,
            operand_place: PlaceOption,
            operand_address: Address,
            operand_snapshot: { ty.to_snapshot(self)? },
            lifetime_perm: Perm
        };
        let new_borrow_lifetime = value.new_borrow_lifetime.to_pure_snapshot(self)?;
        let lifetime_token =
            self.encode_lifetime_token(new_borrow_lifetime.clone(), lifetime_perm.clone().into())?;
        let predicate = self.owned_non_aliased_full_vars_with_snapshot(
            CallContext::BuiltinMethod,
            ty,
            ty,
            &operand_place,
            &operand_address,
            &operand_snapshot,
            position,
        )?;
        let reference_predicate = {
            self.mark_owned_predicate_as_unfolded(result_type)?;
            let mut builder = OwnedNonAliasedUseBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.clone().into(),
                target_address.clone().into(),
                position,
            )?;
            // builder.add_snapshot_argument(result_value.clone().into())?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            let predicate = builder.build()?;
            let mut builder = OwnedNonAliasedSnapCallBuilder::new(
                self,
                CallContext::BuiltinMethod,
                result_type,
                ty,
                target_place.into(),
                target_address.into(),
                position,
            )?;
            builder.add_custom_argument(true.into())?;
            builder.add_custom_argument(new_borrow_lifetime.clone().into())?;
            builder.add_lifetime_arguments()?;
            builder.add_const_arguments()?;
            let snapshot = builder.build()?;
            expr! { [predicate] && (result_value == [snapshot]) }
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
            let restored_predicate = self.owned_non_aliased_with_snapshot(
                CallContext::BuiltinMethod,
                ty,
                ty,
                operand_place.clone().into(),
                operand_address.clone().into(),
                restoration_snapshot.clone(),
                None,
                position,
            )?;
            let validity =
                self.encode_snapshot_valid_call_for_type(restoration_snapshot.clone(), ty)?;
            let mut arguments = vec![
                new_borrow_lifetime.clone().into(),
                operand_place.clone().into(),
                operand_address.clone().into(),
                restoration_snapshot,
            ];
            arguments.extend(self.create_lifetime_arguments(CallContext::BuiltinMethod, ty)?);
            arguments.extend(self.create_const_arguments(CallContext::BuiltinMethod, ty)?);
            self.encode_view_shift_return(
                &format!("end$borrow${}", ty.get_identifier()),
                arguments,
                vec![expr! { acc(DeadLifetimeToken(new_borrow_lifetime)) }],
                vec![
                    restored_predicate,
                    validity,
                    // DeadLifetimeToken is duplicable and does not get consumed.
                    expr! { acc(DeadLifetimeToken(new_borrow_lifetime)) },
                ],
                vir_low::PredicateKind::EndBorrowViewShift,
                position,
            )?
            // expr! {
            //     wand(
            //         (acc(DeadLifetimeToken(new_borrow_lifetime))) --* (
            //             [restored_predicate] &&
            //             [validity] &&
            //             // DeadLifetimeToken is duplicable and does not get consumed.
            //             (acc(DeadLifetimeToken(new_borrow_lifetime)))
            //         )
            //     )
            // }
        };
        let reference_target_address =
            self.reference_address(result_type, result_value.clone().into(), position)?;
        posts.push(expr! {
            operand_address == [reference_target_address]
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
        parameters.push(operand_address);
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
        position: vir_low::Position,
        add_lifetime_parameters: bool,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        use vir_low::macros::*;
        let snapshot = self.encode_assign_operand_snapshot(operand_counter, operand)?;
        let ty = operand.expression.get_type();
        match operand.kind {
            vir_mid::OperandKind::Copy | vir_mid::OperandKind::Move => {
                let place = self.encode_assign_operand_place(operand_counter)?;
                let address = self.encode_assign_operand_address(operand_counter)?;
                let predicate = self.owned_non_aliased_full_vars_with_snapshot(
                    CallContext::BuiltinMethod,
                    ty,
                    ty,
                    &place,
                    &address,
                    &snapshot,
                    position,
                )?;
                pres.push(predicate.clone());
                let post_predicate = if operand.kind == vir_mid::OperandKind::Copy {
                    predicate
                } else {
                    // let compute_address = ty!(Address);
                    let size_of = self.encode_type_size_expression2(ty, ty)?;
                    // expr! { acc(MemoryBlock((ComputeAddress::compute_address(place, root_address)), [size_of])) }
                    expr! { acc(MemoryBlock(address, [size_of])) }
                };
                posts.push(post_predicate);
                parameters.push(place);
                parameters.push(address);
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
            self.place_option_type()?,
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
    fn encode_memory_block_range_split_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_memory_block_range_join_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()>;

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
    fn encode_havoc_unique_ref_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
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
    fn get_reborrow_target_variable(
        &self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<(vir_low::VariableDecl, vir_mid::Type)>;
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
    fn encode_restore_raw_borrowed_method(
        &mut self,
        ty: &vir_mid::Type,
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
    fn encode_stash_range_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        pointer_value: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        label: String,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;

    fn encode_restore_stash_range_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        old_pointer_value: vir_low::Expression,
        old_start_index: vir_low::Expression,
        old_end_index: vir_low::Expression,
        label: String,
        new_address: vir_low::Expression,
        new_start_index: vir_low::Expression,
        new_end_index: vir_low::Expression,
        position: vir_low::Position,
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
            let source_owned = builder.create_source_owned(false)?;
            builder.add_precondition(source_owned);
            let target_owned = builder.create_target_owned(false)?;
            builder.add_postcondition(target_owned);
            let source_memory_block = builder.create_source_memory_block()?;
            builder.add_postcondition(source_memory_block);
            // builder.add_source_bytes_unchanged_postcondition()?; FIXME – is this needed?
            builder.add_target_validity_postcondition()?;
            if has_body {
                builder.create_body();
                let source_owned = builder.create_source_owned(true)?;
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
                    uniqueness,
                    lifetimes,
                    ..
                }) => {
                    builder.add_memory_block_copy_call()?;
                    if uniqueness.is_unique() {
                        builder.change_unique_ref_place()?;
                    } else {
                        // FIXME: Have a getter for the first lifetime.
                        let lifetime = &lifetimes[0];
                        builder.duplicate_frac_ref(lifetime)?;
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
                let target_owned = builder.create_target_owned(true)?;
                builder.add_statement(vir_low::Statement::fold_no_pos(target_owned));
                if let vir_mid::TypeDecl::Reference(vir_mid::type_decl::Reference {
                    uniqueness,
                    lifetimes,
                    ..
                }) = &type_decl
                {
                    if uniqueness.is_unique() {
                        // FIXME: Have a getter for the first lifetime.
                        let lifetime = &lifetimes[0];
                        builder.add_dead_lifetime_hack(lifetime)?;
                    }
                }
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
            builder.add_permission_amount_positive_precondition()?;
            // builder.add_same_address_precondition()?;
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
                BuiltinMethodKind::CopyPlace,
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
            let target_owned = builder.create_target_owned(false)?;
            builder.add_postcondition(target_owned);
            builder.add_target_validity_postcondition()?;
            if has_body {
                builder.create_body();
                let source_owned = builder.create_source_owned_predicate()?;
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
                    uniqueness,
                    lifetimes,
                    ..
                }) => {
                    // FIXME: Have a getter for the first lifetime.
                    let lifetime = &lifetimes[0];
                    assert!(uniqueness.is_shared());
                    builder.add_memory_block_copy_call()?;
                    builder.duplicate_frac_ref(lifetime)?;
                }
                vir_mid::TypeDecl::Struct(decl) => {
                    builder.add_split_target_memory_block_call()?;
                    for field in &decl.fields {
                        builder.add_copy_place_call_for_field(field)?;
                    }
                }
                vir_mid::TypeDecl::Trusted(_) | vir_mid::TypeDecl::TypeVar(_) => {
                    assert!(!has_body);
                }
                _ => unimplemented!("{type_decl:?}"),
            }
            if has_body {
                let target_owned = builder.create_target_owned(true)?;
                builder.add_statement(vir_low::Statement::fold_no_pos(target_owned));
                let source_owned = builder.create_source_owned_predicate()?;
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
            let target_owned = builder.create_target_owned(false)?;
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
                let target_owned = builder.create_target_owned(true)?;
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
                place: PlaceOption,
                root_address: Address,
                old_snapshot: {ty.to_snapshot(self)?},
                fresh_snapshot: {ty.to_snapshot(self)?}
            };
            let position = vir_low::Position::default();
            let validity =
                self.encode_snapshot_valid_call_for_type(fresh_snapshot.clone().into(), ty)?;
            let mut parameters = vec![place.clone(), root_address.clone(), old_snapshot.clone()];
            parameters.extend(self.create_lifetime_parameters(&type_decl)?);
            let predicate_in = self.owned_non_aliased_full_vars_with_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &old_snapshot,
                position,
            )?;
            let predicate_out = self.owned_non_aliased_full_vars_with_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &fresh_snapshot,
                position,
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
    fn encode_havoc_unique_ref_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_unique_ref_havoc_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_unique_ref_havoc_methods
                .insert(ty_identifier);
            use vir_low::macros::*;
            let method_name = self.encode_havoc_unique_ref_method_name(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            var_decls! {
                place: PlaceOption,
                root_address: Address,
                lifetime: Lifetime,
                fresh_snapshot: {ty.to_snapshot(self)?}
            };
            let position = vir_low::Position::default();
            let validity =
                self.encode_snapshot_valid_call_for_type(fresh_snapshot.clone().into(), ty)?;
            let mut parameters = vec![place.clone(), root_address.clone(), lifetime.clone()];
            parameters.extend(self.create_lifetime_parameters(&type_decl)?);
            let TODO_target_slice_len = None;
            let predicate_in = self.unique_ref_full_vars(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &lifetime,
                TODO_target_slice_len.clone(),
                position,
            )?;
            let predicate_out = self.unique_ref_full_vars_with_current_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &root_address,
                &fresh_snapshot,
                &lifetime,
                TODO_target_slice_len,
                position,
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

            self.encode_compute_address(ty)?;

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
    fn encode_memory_block_range_split_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_memory_block_range_split_methods
            .contains(&ty_identifier)
        {
            // assert!(
            //     !ty.is_trusted() && !ty.is_type_var(),
            //     "Trying to split an abstract type."
            // );
            self.builtin_methods_state
                .encoded_memory_block_range_split_methods
                .insert(ty_identifier);

            self.encode_compute_address(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = MemoryBlockRangeSplitMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "memory_block_range_split",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::JoinMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_whole_memory_block_precondition()?;
            builder.add_memory_block_range_postcondition()?;
            builder.add_byte_values_preserved_postcondition()?;
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

            self.encode_compute_address(ty)?;
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
    fn encode_memory_block_range_join_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_memory_block_range_join_methods
            .contains(&ty_identifier)
        {
            // assert!(
            //     !ty.is_trusted() && !ty.is_type_var(),
            //     "Trying to join an abstract type."
            // );
            self.builtin_methods_state
                .encoded_memory_block_range_join_methods
                .insert(ty_identifier);

            self.encode_compute_address(ty)?;
            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();
            let mut builder = MemoryBlockRangeJoinMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "memory_block_range_join",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::JoinMemoryBlock,
            )?;
            builder.create_parameters()?;
            builder.add_memory_block_range_precondition()?;
            builder.add_whole_memory_block_postcondition()?;
            builder.add_byte_values_preserved_postcondition()?;
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

            self.mark_owned_predicate_as_unfolded(ty)?;

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
            let predicate = builder.create_owned(false)?;
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
                let predicate = builder.create_owned(true)?;
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
            if has_body {}
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
        let target_address = self.encode_expression_as_place_address(&target)?;
        // let target_address = self.extract_root_address(&target)?;
        let mut arguments = vec![target_place.clone(), target_address.clone()];
        self.encode_rvalue_arguments(&target, &mut arguments, &value)?;
        let target_value_type = target.get_type().to_snapshot(self)?;
        let result_value = self.create_new_temporary_variable(target_value_type)?;
        let position = match &value {
            vir_mid::Rvalue::CheckedBinaryOp(_) => self
                .encoder
                .change_error_context(position, ErrorCtxt::CheckedBinaryOpPrecondition),
            _ => position,
        };
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
            // let source_root_address = self.extract_root_address(&source)?;
            let source_address = self.encode_expression_as_place_address(&source)?;
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
                source_address,
                source_snapshot.clone(),
                source_permission_amount,
            )?];
            let new_snapshot = self.encode_snapshot_update_with_new_snapshot(
                &mut copy_place_statements,
                &target,
                source_snapshot,
                position,
                // Some(new_snapshot.clone()),
            )?;
            if let Some(conditions) = value.use_field {
                let mut disjuncts = Vec::new();
                for condition in conditions {
                    disjuncts.push(self.lower_block_marker_condition(condition)?);
                }
                let mut else_branch = vec![assign_statement];
                let new_snapshot_else_branch = self.encode_snapshot_update_with_new_snapshot(
                    &mut else_branch,
                    &target,
                    result_value.into(),
                    position,
                    // Some(new_snapshot),
                )?;
                statements.push(vir_low::Statement::conditional(
                    disjuncts.into_iter().disjoin(),
                    copy_place_statements,
                    else_branch,
                    position,
                ));
                statements.push(vir_low::Statement::assume(
                    vir_low::Expression::equals(new_snapshot, new_snapshot_else_branch),
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
            // if let vir_mid::Rvalue::Ref(value) = value {
            //     let snapshot = if value.uniqueness.is_unique() {
            //         self.reference_target_final_snapshot(
            //             target.get_type(),
            //             result_value.into(),
            //             position,
            //         )?
            //     } else {
            //         self.reference_target_current_snapshot(
            //             target.get_type(),
            //             result_value.into(),
            //             position,
            //         )?
            //     };
            //     self.encode_snapshot_update(statements, &value.place, snapshot, position)?;
            // }
            match value {
                vir_mid::Rvalue::Ref(value) => {
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
                vir_mid::Rvalue::Reborrow(value) => {
                    assert!(self
                        .builtin_methods_state
                        .reborrow_target_variables
                        .insert(
                            value.new_borrow_lifetime,
                            (result_value, target.get_type().clone())
                        )
                        .is_none());
                }
                // vir_mid::Rvalue::AddressOf(value) => {
                //     let address = self.pointer_address(
                //         target.get_type(),
                //         result_value.clone().into(),
                //         position,
                //     )?;
                //     let heap = self.heap_variable_version_at_label(&None)?;
                //     // statements.push(vir_low::Statement::assume(
                //     //     vir_low::Expression::container_op_no_pos(
                //     //         vir_low::ContainerOpKind::MapContains,
                //     //         heap.ty.clone(),
                //     //         vec![heap.into(), address],
                //     //     ),
                //     //     position,
                //     // ));
                //     let heap_chunk = self.pointer_target_snapshot(
                //         target.get_type(),
                //         &None,
                //         result_value.into(),
                //         position,
                //     )?;
                //     statements.push(vir_low::Statement::assume(
                //         vir_low::Expression::equals(
                //             heap_chunk,
                //             value.place.to_procedure_snapshot(self)?,
                //         ),
                //         position,
                //     ));
                // }
                _ => {}
            }
        }
        Ok(())
    }
    fn get_reborrow_target_variable(
        &self,
        lifetime: &vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<(vir_low::VariableDecl, vir_mid::Type)> {
        let variable_with_type = self
            .builtin_methods_state
            .reborrow_target_variables
            .get(lifetime)
            .cloned()
            .unwrap();
        Ok(variable_with_type)
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
        {
            // Mark the produced MemoryBlock as non-aliasable instance.
            assert!(
                matches!(operand.kind, vir_mid::OperandKind::Move | vir_mid::OperandKind::Constant),
                "Our assumption that all consume operands are either moves or constants is wrong: {operand}."
            );
            if vir_mid::OperandKind::Move == operand.kind
                && !operand.expression.is_behind_pointer_dereference()
            {
                // assert!(
                //     operand.expression.is_local(),
                //     "Our assumption that all consume operands are moves of locals is wrong: {operand}."
                // );
                self.mark_place_as_used_in_memory_block(&operand.expression)?;
            }
            // let ty = operand.expression.get_type();
            // let address = self.encode_expression_as_place_address(&operand.expression)?;
            // let size = self.encode_type_size_expression2(ty, ty)?;
            // let predicate_acc = self
            //     .encode_memory_block_acc(address, size, position)?
            //     .unwrap_predicate_access_predicate();
            // self.mark_predicate_as_non_aliased(predicate_acc)?;
        }
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
                self.mark_owned_predicate_as_unfolded(ty)?;
                let place = self.encode_expression_as_place(&predicate.place)?;
                // let address = self.extract_root_address(&predicate.place)?;
                let address = self.encode_expression_as_place_address(&predicate.place)?;
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
            vir_mid::Predicate::UniqueRef(predicate) => {
                let ty = predicate.place.get_type();
                self.encode_havoc_unique_ref_method(ty)?;
                self.mark_unique_ref_as_used(ty)?;
                let lifetime =
                    self.encode_lifetime_const_into_procedure_variable(predicate.lifetime)?;
                let place = self.encode_expression_as_place(&predicate.place)?;
                let address = self.encode_expression_as_place_address(&predicate.place)?;
                let snapshot_type = ty.to_snapshot(self)?;
                let fresh_snapshot = self.create_new_temporary_variable(snapshot_type)?;
                let method_name = self.encode_havoc_unique_ref_method_name(ty)?;
                let mut arguments = vec![place, address, lifetime.into()];
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
            vir_mid::Predicate::FracRef(_) => {
                // Fractional references are immutable, so havoc is a no-op.
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
                place: PlaceOption,
                address: Address,
                current_snapshot: {ty.to_snapshot(self)?}
            };
            let position = vir_low::Position::default();
            let lifetime_access = expr! { acc(LifetimeToken(lifetime), lifetime_perm) };
            let TODO_target_slice_len = None;
            let frac_ref_access = self.frac_ref_full_vars_with_current_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &address,
                &current_snapshot,
                &lifetime,
                TODO_target_slice_len.clone(),
                position,
            )?;
            let prestate_snapshot = vir_low::Expression::labelled_old_no_pos(
                None,
                self.frac_ref_snap(
                    CallContext::BuiltinMethod,
                    ty,
                    &type_decl,
                    place.clone().into(),
                    address.clone().into(),
                    lifetime.clone().into(),
                    TODO_target_slice_len,
                    position,
                )?,
            );
            let owned_access = self.owned_non_aliased_with_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                place.clone().into(),
                address.clone().into(),
                prestate_snapshot,
                Some(owned_perm.clone().into()),
                position,
            )?;
            let owned_access_viewshift = self.owned_non_aliased(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                place.clone().into(),
                address.clone().into(),
                Some(owned_perm.clone().into()),
                position,
            )?;
            let mut parameters = vec![
                lifetime.clone(),
                lifetime_perm.clone(),
                place.clone(),
                address.clone(),
                current_snapshot.clone(),
            ];
            parameters.extend(self.create_lifetime_parameters(&type_decl)?);
            parameters.extend(self.create_const_parameters(&type_decl)?);
            let close_frac_ref_predicate = expr! {
                acc(CloseFracRef<ty>(
                    lifetime,
                    lifetime_perm,
                    place,
                    address,
                    current_snapshot,
                    owned_perm
                ))
            };
            let lifetime_perm_bounds = expr! {
                ([vir_low::Expression::no_permission()] < lifetime_perm) &&
                (lifetime_perm < [vir_low::Expression::full_permission()])
            };
            let owned_perm_bounds = expr! {
                ([vir_low::Expression::no_permission()] < owned_perm) &&
                (owned_perm < [vir_low::Expression::full_permission()])
            };
            let method = vir_low::MethodDecl::new(
                self.encode_open_frac_bor_atomic_method_name(ty)?,
                vir_low::MethodKind::MirOperation,
                parameters,
                vec![owned_perm.clone()],
                vec![
                    lifetime_perm_bounds.clone(),
                    lifetime_access.clone(),
                    frac_ref_access.clone(),
                ],
                vec![
                    owned_perm_bounds.clone(),
                    owned_access,
                    close_frac_ref_predicate.clone(),
                    // vir_low::Expression::magic_wand_no_pos(
                    //     owned_access_viewshift,
                    //     expr! { [lifetime_access] && [frac_ref_access] },
                    // ),
                ],
                None,
            );
            self.declare_method(method)?;
            {
                let close_frac_ref_predicate_decl = vir_low::PredicateDecl::new(
                    predicate_name! { CloseFracRef<ty> },
                    vir_low::PredicateKind::CloseFracRef,
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        place.clone(),
                        address.clone(),
                        current_snapshot.clone(),
                        owned_perm.clone(),
                    ],
                    None,
                );
                self.declare_predicate(close_frac_ref_predicate_decl)?;
                let mut parameters = vec![
                    lifetime.clone(),
                    lifetime_perm,
                    place.clone(),
                    address.clone(),
                    current_snapshot.clone(),
                    owned_perm,
                ];
                parameters.extend(self.create_lifetime_parameters(&type_decl)?);
                parameters.extend(self.create_const_parameters(&type_decl)?);
                // Apply the viewshift encoded in the `CloseFracRef` predicate.
                let close_method = vir_low::MethodDecl::new(
                    method_name! { close_frac_ref<ty> },
                    vir_low::MethodKind::MirOperation,
                    parameters,
                    Vec::new(),
                    vec![
                        lifetime_perm_bounds,
                        owned_perm_bounds,
                        close_frac_ref_predicate,
                        owned_access_viewshift,
                    ],
                    vec![lifetime_access, frac_ref_access],
                    None,
                );
                self.declare_method(close_method)?;
            }
        }
        Ok(())
    }

    fn encode_restore_raw_borrowed_method(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<()> {
        let ty_identifier = ty.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_restore_raw_borrowed_methods
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_restore_raw_borrowed_methods
                .insert(ty_identifier);

            self.encode_restore_raw_borrowed_transition_predicate(ty)?;

            let type_decl = self.encoder.get_type_decl_mid(ty)?;
            let normalized_type = ty.normalize_type();

            let mut builder = RestoreRawBorrowedMethodBuilder::new(
                self,
                vir_low::MethodKind::LowMemoryOperation,
                "restore_raw_borrowed",
                &normalized_type,
                &type_decl,
                BuiltinMethodKind::RestoreRawBorrowed,
            )?;
            builder.create_parameters()?;
            builder.add_aliased_source_precondition()?;
            builder.add_shift_precondition()?;
            builder.add_non_aliased_target_postcondition()?;
            let method = builder.build();
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
                LIFETIME_DOMAIN_NAME,
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
                LIFETIME_DOMAIN_NAME,
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
                place: PlaceOption,
                address: Address,
                current_snapshot: {ty.to_snapshot(self)?},
                final_snapshot: {ty.to_snapshot(self)?}
            };
            let position = vir_low::Position::default();
            let owned_predicate = self.owned_non_aliased_full_vars_with_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &address,
                &current_snapshot,
                position,
            )?;
            let unique_ref_predicate = self.unique_ref_full_vars_with_current_snapshot(
                CallContext::BuiltinMethod,
                ty,
                &type_decl,
                &place,
                &address,
                &current_snapshot,
                &lifetime,
                None,
                position,
            )?;
            let open_method = vir_low::MethodDecl::new(
                method_name! { open_mut_ref<ty> },
                vir_low::MethodKind::MirOperation,
                vec![
                    lifetime.clone(),
                    lifetime_perm.clone(),
                    place.clone(),
                    address.clone(),
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
                        address,
                        final_snapshot
                    ))},
                ],
                None,
            );
            self.declare_method(open_method)?;

            {
                let close_mut_ref_predicate = vir_low::PredicateDecl::new(
                    predicate_name! { CloseMutRef<ty> },
                    vir_low::PredicateKind::WithoutSnapshotWhole,
                    vec![
                        lifetime.clone(),
                        lifetime_perm.clone(),
                        place.clone(),
                        address.clone(),
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
                        address.clone(),
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
                            address,
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
                place: PlaceOption,
                address: Address,
                current_snapshot: {target_type.to_snapshot(self)?},
                final_snapshot: {target_type.to_snapshot(self)?}
            }
            let mut parameters = vec![
                lft.clone(),
                old_lft.clone(),
                lifetime_perm.clone(),
                place.clone(),
                address.clone(),
                current_snapshot.clone(),
            ];
            if reference_type.uniqueness.is_unique() {
                parameters.push(final_snapshot);
            }
            let position = vir_low::Position::default();
            let mut pres = vec![
                expr! { [vir_low::Expression::no_permission()] < lifetime_perm },
                expr! { lifetime_perm < [vir_low::Expression::full_permission()] },
                expr! { Lifetime::included([lft.clone().into()], [old_lft.clone().into()])},
                expr! { acc(LifetimeToken(lft), lifetime_perm)},
            ];
            let mut posts = vec![expr! { acc(LifetimeToken(lft), lifetime_perm)}];
            if reference_type.uniqueness.is_unique() {
                pres.push(self.unique_ref_full_vars_with_current_snapshot(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &address,
                    &current_snapshot,
                    &old_lft,
                    None,
                    position,
                )?);
                posts.push(self.unique_ref_full_vars_with_current_snapshot(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &address,
                    &current_snapshot,
                    &lft,
                    None,
                    position,
                )?);
                let old_final_snapshot = self.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    place.clone().into(),
                    address.clone().into(),
                    old_lft.clone().into(),
                    None,
                    true,
                    position,
                )?;
                let new_final_snapshot = self.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    place.clone().into(),
                    address.clone().into(),
                    lft.clone().into(),
                    None,
                    true,
                    position,
                )?;
                posts.push(expr! { [old_final_snapshot] == [new_final_snapshot] });
            } else {
                pres.push(self.frac_ref_full_vars_with_current_snapshot(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &address,
                    &current_snapshot,
                    &old_lft,
                    None,
                    position,
                )?);
                posts.push(self.frac_ref_full_vars_with_current_snapshot(
                    CallContext::BuiltinMethod,
                    target_type,
                    target_type,
                    &place,
                    &address,
                    &current_snapshot,
                    &lft,
                    None,
                    position,
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

    fn encode_stash_range_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        pointer_value: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        label: String,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        statements.push(vir_low::Statement::comment(format!(
            "Stash range call for {label}"
        )));
        // statements.push(vir_low::Statement::label(label.clone(), position));
        let exhale_owned = vir_low::Statement::exhale(
            self.owned_aliased_range(
                CallContext::Procedure,
                ty,
                ty,
                pointer_value.clone(),
                start_index.clone(),
                end_index.clone(),
                None,
                position,
            )?,
            position,
        );
        statements.push(exhale_owned);
        let vir_mid::Type::Pointer(pointer_type) = ty else {
            unreachable!("ty: {}", ty);
        };
        let target_type = &*pointer_type.target_type;
        let ty_identifier = target_type.get_identifier();
        if !self
            .builtin_methods_state
            .encoded_stashed_owned_aliased_predicates
            .contains(&ty_identifier)
        {
            self.builtin_methods_state
                .encoded_stashed_owned_aliased_predicates
                .insert(ty_identifier);
            let predicate = vir_low::PredicateDecl::new(
                predicate_name! { StashedOwnedAliased<target_type> },
                vir_low::PredicateKind::WithoutSnapshotWhole,
                vec![
                    var! { index: Int },
                    var! { bytes: Bytes },
                    var! { snapshot: { target_type.to_snapshot(self)? } },
                ],
                None,
            );
            self.declare_predicate(predicate)?;
        }
        let start_address = self.pointer_address(ty, pointer_value, position)?;
        let size = self.encode_type_size_expression2(target_type, target_type)?;
        let inhale_raw = vir_low::Statement::inhale(
            self.encode_memory_block_range_acc(
                start_address.clone(),
                size.clone(),
                start_index.clone(),
                end_index.clone(),
                position,
            )?,
            position,
        );
        statements.push(inhale_raw);
        let inhale_stash = {
            let size_type = self.size_type_mid()?;
            var_decls! {
                index: Int
            }
            // let start_address = self.pointer_address(
            //     ty,
            //     pointer_value,
            //     position,
            // )?;
            let element_address =
                self.address_offset(size.clone(), start_address, index.clone().into(), position)?;
            let start_index = self.obtain_constant_value(&size_type, start_index, position)?;
            let end_index = self.obtain_constant_value(&size_type, end_index, position)?;
            let bytes = self.encode_memory_block_bytes_expression(element_address.clone(), size)?;
            let snapshot = vir_low::Expression::labelled_old(
                Some(label),
                self.owned_aliased_snap(
                    CallContext::Procedure,
                    target_type,
                    target_type,
                    element_address.clone(),
                    position,
                )?,
                position,
            );
            let stash_predicate = expr! {
                acc(StashedOwnedAliased<target_type>(
                    index,
                    [bytes],
                    [snapshot]
                ))
            };
            let body = expr!(
                (([start_index] <= index) && (index < [end_index])) ==>
                [stash_predicate]
            );
            let expression = vir_low::Expression::forall(
                vec![index],
                vec![vir_low::Trigger::new(vec![element_address])],
                body,
            );
            vir_low::Statement::inhale(expression, position)
        };
        statements.push(inhale_stash);
        // statements.push(vir_low::Statement::label(
        //     format!("{}$post", label),
        //     position,
        // ));
        Ok(())
    }

    fn encode_restore_stash_range_call(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        old_pointer_value: vir_low::Expression,
        old_start_index: vir_low::Expression,
        old_end_index: vir_low::Expression,
        label: String,
        new_pointer_value: vir_low::Expression,
        new_start_index_usize: vir_low::Expression,
        new_end_index_usize: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        statements.push(vir_low::Statement::comment(format!(
            "Restore stash for {label}"
        )));
        let label_post = format!("{label}$post");
        use vir_low::macros::*;
        let vir_mid::Type::Pointer(pointer_type) = ty else {
            unreachable!("ty: {}", ty);
        };
        let size_type = self.size_type_mid()?;
        let target_type = &*pointer_type.target_type;
        let size = self.encode_type_size_expression2(target_type, target_type)?;
        let old_start_address = self.pointer_address(ty, old_pointer_value, position)?;
        let new_start_address = self.pointer_address(ty, new_pointer_value.clone(), position)?;
        let new_start_index =
            self.obtain_constant_value(&size_type, new_start_index_usize.clone(), position)?;
        let new_end_index =
            self.obtain_constant_value(&size_type, new_end_index_usize.clone(), position)?;
        // let new_end_index = vir_low::Expression::add(
        //     new_start_index.clone(),
        //     vir_low::Expression::labelled_old(
        //         Some(label.clone()),
        //         vir_low::Expression::subtract(
        //             self.obtain_constant_value(&size_type, old_end_index, position)?,
        //             self.obtain_constant_value(&size_type, old_start_index.clone(), position)?,
        //         ),
        //         position,
        //     ),
        // );
        {
            // For performance reasons, we do not have global extensionality
            // assumptions, but assume them when needed.

            // FIXME: Instead of having the assumption as a quantifier, assert
            // that bytes are equal for the entire range and then assume that
            // the byte blocks are equal.
            var_decls! {
                index: Int,
                byte_index: Int
            }
            let new_element_address = self.address_offset(
                size.clone(),
                new_start_address.clone(),
                index.clone().into(),
                position,
            )?;
            let old_index = vir_low::Expression::add(
                vir_low::Expression::labelled_old(
                    Some(label.clone()),
                    self.obtain_constant_value(&size_type, old_start_index.clone(), position)?,
                    position,
                ),
                vir_low::Expression::subtract(index.clone().into(), new_start_index.clone()),
            );
            let old_element_address =
                self.address_offset(size.clone(), old_start_address.clone(), old_index, position)?;
            let new_block_bytes = self
                .encode_memory_block_bytes_expression(new_element_address.clone(), size.clone())?;
            let old_block_bytes =
                self.encode_memory_block_bytes_expression(old_element_address, size.clone())?;
            let old_block_bytes =
                vir_low::Expression::labelled_old(Some(label_post), old_block_bytes, position);
            let element_size_int =
                self.obtain_constant_value(&size_type, size.clone(), position)?;
            let new_read_element_byte = self.encode_read_byte_expression_int(
                new_block_bytes.clone(),
                byte_index.clone().into(),
                position,
            )?;
            let old_read_element_byte = self.encode_read_byte_expression_int(
                old_block_bytes.clone(),
                byte_index.clone().into(),
                position,
            )?;
            let memory_block_range_join_trigger = self.call_trigger_function(
                "memory_block_range_join_trigger",
                vec![index.clone().into(), byte_index.clone().into()],
                position,
            )?;
            let bytes_equal_body = expr!(
                ((([new_start_index.clone()] <= index) && (index < [new_end_index.clone()])) &&
                (([0.into()] <= byte_index) && (byte_index < [element_size_int]))) ==>
                ([memory_block_range_join_trigger] &&
                    ([new_read_element_byte.clone()] == [old_read_element_byte]))
            );
            let bytes_equal = vir_low::Expression::forall(
                vec![index.clone(), byte_index],
                vec![vir_low::Trigger::new(vec![new_read_element_byte])],
                bytes_equal_body,
            );
            let assert_byte_equality =
                vir_low::Statement::assert_no_pos(bytes_equal).set_default_position(position);
            statements.push(assert_byte_equality);
            let body = expr!(
                (([new_start_index.clone()] <= index) && (index < [new_end_index.clone()])) ==>
                // (
                    ([new_block_bytes] == [old_block_bytes])
                //  == [bytes_equal])
            );
            let expression = vir_low::Expression::forall(
                vec![index],
                vec![vir_low::Trigger::new(vec![new_element_address])],
                body,
            );
            let assume_extensionality = vir_low::Statement::assume(expression, position);
            statements.push(assume_extensionality);
        };
        let exhale_stash = {
            var_decls! {
                index: Int
            }
            // let start_address = self.pointer_address(
            //     ty,
            //     pointer_value,
            //     position,
            // )?;
            let old_index = vir_low::Expression::add(
                vir_low::Expression::labelled_old(
                    Some(label.clone()),
                    self.obtain_constant_value(&size_type, old_start_index.clone(), position)?,
                    position,
                ),
                vir_low::Expression::subtract(index.clone().into(), new_start_index.clone()),
            );
            let old_element_address = self.address_offset(
                size.clone(),
                old_start_address.clone(),
                old_index.clone(),
                position,
            )?;
            let new_element_address = self.address_offset(
                size.clone(),
                new_start_address.clone(),
                index.clone().into(),
                position,
            )?;
            // let start_index = self.obtain_constant_value(&size_type, start_index, position)?;
            // let end_index = self.obtain_constant_value(&size_type, end_index, position)?;
            let bytes = self
                .encode_memory_block_bytes_expression(new_element_address.clone(), size.clone())?;
            let snapshot = vir_low::Expression::labelled_old(
                Some(label.clone()),
                self.owned_aliased_snap(
                    CallContext::Procedure,
                    target_type,
                    target_type,
                    old_element_address,
                    position,
                )?,
                position,
            );
            let stash_predicate = expr! {
                acc(StashedOwnedAliased<target_type>(
                    [old_index],
                    [bytes],
                    [snapshot]
                ))
            };
            let body = expr!(
                (([new_start_index.clone()] <= index) && (index < [new_end_index.clone()])) ==>
                [stash_predicate]
            );
            let expression = vir_low::Expression::forall(
                vec![index],
                vec![vir_low::Trigger::new(vec![new_element_address])],
                body,
            );
            vir_low::Statement::exhale(expression, position)
        };
        statements.push(exhale_stash);
        // FIXME: Code duplication with encode_memory_block_range_acc.
        let exhale_raw = {
            // var_decls! {
            //     index: Int
            // }
            // let element_address = self.address_offset(
            //     size.clone(),
            //     new_start_address.clone(),
            //     index.clone().into(),
            //     position,
            // )?;
            // let predicate =
            //     self.encode_memory_block_acc(element_address.clone(), size.clone(), position)?;
            // // let new_start_index = self.obtain_constant_value(&size_type, new_start_address.clone(), position)?;
            // // let end_index = self.obtain_constant_value(&size_type, end_index, position)?;
            // let body = expr!(
            //     (([new_start_index.clone()] <= index) && (index < [new_end_index.clone()])) ==> [predicate]
            // );
            // let expression = vir_low::Expression::forall(
            //     vec![index],
            //     vec![vir_low::Trigger::new(vec![element_address])],
            //     body,
            // );
            let expression = self.encode_memory_block_range_acc(
                new_start_address.clone(),
                size.clone(),
                new_start_index_usize.clone(),
                new_end_index_usize.clone(),
                position,
            )?;
            vir_low::Statement::exhale(
                expression,
                // self.encode_memory_block_range_acc(
                //     new_start_address.clone(),
                //     size,
                //     new_start_index.clone(),
                //     new_end_index.clone(),
                //     position,
                // )?,
                position,
            )
        };
        statements.push(exhale_raw);
        let inhale_owned = {
            // var_decls! {
            //     index: Int
            // }
            // let element_address = self.address_offset(
            //     size.clone(),
            //     new_start_address.clone(),
            //     index.clone().into(),
            //     position,
            // )?;
            // let predicate = self.owned_aliased(
            //     CallContext::Procedure,
            //     target_type,
            //     target_type,
            //     element_address.clone(),
            //     None,
            //     position,
            // )?;
            // // let new_start_index = self.obtain_constant_value(&size_type, new_start_address.clone(), position)?;
            // // let end_index = self.obtain_constant_value(&size_type, end_index, position)?;
            // let body = expr!(
            //     (([new_start_index.clone()] <= index) && (index < [new_end_index.clone()])) ==>
            //     [predicate]
            // );
            // let expression = vir_low::Expression::forall(
            //     vec![index],
            //     vec![vir_low::Trigger::new(vec![element_address])],
            //     body,
            // );
            let expression = self.owned_aliased_range(
                CallContext::Procedure,
                ty,
                ty,
                new_pointer_value.clone(),
                new_start_index_usize.clone(),
                new_end_index_usize.clone(),
                None,
                position,
            )?;
            vir_low::Statement::inhale(expression, position)
        };
        statements.push(inhale_owned);
        let inhale_snapshot_preserved = {
            var_decls! {
                index: Int
            }
            let new_element_address = self.address_offset(
                size.clone(),
                new_start_address,
                index.clone().into(),
                position,
            )?;
            let old_index = vir_low::Expression::add(
                vir_low::Expression::labelled_old(
                    Some(label.clone()),
                    self.obtain_constant_value(&size_type, old_start_index, position)?,
                    position,
                ),
                vir_low::Expression::subtract(index.clone().into(), new_start_index.clone()),
            );
            let old_element_address =
                self.address_offset(size, old_start_address, old_index, position)?;
            let new_snapshot = self.owned_aliased_snap(
                CallContext::Procedure,
                target_type,
                target_type,
                new_element_address.clone(),
                position,
            )?;
            let old_snapshot = self.owned_aliased_snap(
                CallContext::Procedure,
                target_type,
                target_type,
                old_element_address,
                position,
            )?;
            let old_snapshot =
                vir_low::Expression::labelled_old(Some(label), old_snapshot, position);
            let body = expr!(
                (([new_start_index] <= index) && (index < [new_end_index])) ==>
                ([new_snapshot] == [old_snapshot])
            );
            let expression = vir_low::Expression::forall(
                vec![index],
                vec![vir_low::Trigger::new(vec![new_element_address])],
                body,
            );
            vir_low::Statement::inhale(expression, position)
        };
        statements.push(inhale_snapshot_preserved);
        Ok(())
    }
}
