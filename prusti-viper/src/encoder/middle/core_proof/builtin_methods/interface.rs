use super::helpers::ToAddressWriter;
use crate::encoder::{
    errors::{BuiltinMethodKind, ErrorCtxt, SpannedEncodingResult},
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        builtin_methods::split_join::SplitJoinHelper,
        compute_address::ComputeAddressInterface,
        errors::ErrorsInterface,
        fold_unfold::FoldUnfoldInterface,
        lowerer::{Lowerer, MethodsLowererInterface},
        predicates_memory_block::PredicatesMemoryBlockInterface,
        snapshots::{IntoSnapshot, SnapshotsInterface},
        type_layouts::TypeLayoutsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use rustc_hash::FxHashSet;

use vir_crate::{common::expression::ExpressionIterator, low as vir_low, middle as vir_mid};

#[derive(Default)]
pub(in super::super) struct BuiltinMethodsState {
    encoded_write_place_methods: FxHashSet<vir_mid::Type>,
    encoded_move_place_methods: FxHashSet<vir_mid::Type>,
    encoded_write_address_methods: FxHashSet<vir_mid::Type>,
    encoded_memory_block_split_methods: FxHashSet<vir_mid::Type>,
    encoded_memory_block_join_methods: FxHashSet<vir_mid::Type>,
}

trait Private {
    fn encode_fully_split_write_address(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        value: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
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
}

pub(in super::super) trait BuiltinMethodsInterface {
    fn encode_write_address_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_move_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_write_place_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
    fn encode_memory_block_split_method(&mut self, ty: &vir_mid::Type)
        -> SpannedEncodingResult<()>;
    fn encode_memory_block_join_method(&mut self, ty: &vir_mid::Type) -> SpannedEncodingResult<()>;
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
}
