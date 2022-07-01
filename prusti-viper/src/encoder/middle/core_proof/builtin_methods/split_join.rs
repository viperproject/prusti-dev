use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        compute_address::ComputeAddressInterface,
        lowerer::Lowerer,
        predicates::PredicatesMemoryBlockInterface,
        snapshots::{IntoSnapshot, SnapshotBytesInterface, SnapshotValuesInterface},
        type_layouts::TypeLayoutsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use vir_crate::{low as vir_low, middle as vir_mid};
use vir_low::macros::*;
use vir_mid::{FieldDecl, Type};

pub(super) struct SplitJoinHelper {
    pub(super) preconditions: Vec<vir_low::Expression>,
    pub(super) postconditions: Vec<vir_low::Expression>,
    pub(super) field_to_bytes_equalities: Vec<vir_low::Expression>,
    pub(super) is_joining: bool,
}

impl SplitJoinHelper {
    pub(super) fn new(is_joining: bool) -> Self {
        var_decls! { permission_amount: Perm };
        Self {
            preconditions: vec![
                expr! { [vir_low::Expression::no_permission()] < permission_amount },
            ],
            postconditions: Vec::new(),
            field_to_bytes_equalities: Vec::new(),
            is_joining,
        }
    }
}

type R = SpannedEncodingResult<()>;

impl TypeDeclWalker for SplitJoinHelper {
    type Parameters = ();
    fn before(&mut self, ty: &vir_mid::Type, _: &(), lowerer: &mut Lowerer) -> R {
        lowerer.encode_compute_address(ty)?;
        var_decls!(address: Address, permission_amount: Perm);
        let size_of = lowerer.encode_type_size_expression(ty)?;
        let whole_block = expr!(acc(MemoryBlock(address, [size_of]), permission_amount));
        if self.is_joining {
            self.postconditions.push(whole_block);
        } else {
            self.preconditions.push(whole_block);
        }
        Ok(())
    }
    fn walk_primitive(&mut self, _: &Type, _: &(), _lowerer: &mut Lowerer) -> R {
        unreachable!("Trying to split memory block of a primitive type.");
    }
    fn walk_field(&mut self, ty: &Type, field: &FieldDecl, _: &(), lowerer: &mut Lowerer) -> R {
        let field_size_of = lowerer.encode_type_size_expression(&field.ty)?;
        var_decls!(address: Address, permission_amount: Perm);
        let field_address =
            lowerer.encode_field_address(ty, field, address.into(), Default::default())?;
        {
            // Encode to_bytes equality.
            lowerer.encode_snapshot_to_bytes_function(&field.ty)?;
            let memory_block_field_bytes = lowerer.encode_memory_block_bytes_expression(
                field_address.clone(),
                field_size_of.clone(),
            )?;
            let snapshot = var! { snapshot: {ty.to_snapshot(lowerer)?} }.into();
            let field_snapshot =
                lowerer.obtain_struct_field_snapshot(ty, field, snapshot, Default::default())?;
            let to_bytes = ty! { Bytes };
            if self.is_joining {
                self.field_to_bytes_equalities.push(expr! {
                    (old([memory_block_field_bytes])) == (Snap<(&field.ty)>::to_bytes([field_snapshot]))
                });
            } else {
                self.field_to_bytes_equalities.push(expr! {
                    (([memory_block_field_bytes])) == (Snap<(&field.ty)>::to_bytes([field_snapshot]))
                });
            }
        }
        let field_block = expr! {
            acc(MemoryBlock([field_address], [field_size_of]), permission_amount)
        };
        if self.is_joining {
            self.preconditions.push(field_block);
        } else {
            self.postconditions.push(field_block);
        }
        Ok(())
    }
}
