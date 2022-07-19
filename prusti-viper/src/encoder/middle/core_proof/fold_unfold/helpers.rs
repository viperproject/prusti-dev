use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface, builtin_methods::BuiltinMethodsInterface, lowerer::Lowerer,
        places::PlacesInterface, predicates::PredicatesOwnedInterface,
        snapshots::SnapshotValuesInterface, utils::type_decl_encoder::TypeDeclWalker,
    },
};
use vir_crate::{low as vir_low, middle as vir_mid};
use vir_low::macros::*;
use vir_mid::{FieldDecl, Type};

pub(super) struct OwnedUnFolder<'a> {
    pub(super) statements: &'a mut Vec<vir_low::Statement>,
    pub(super) root_address: &'a vir_low::Expression,
    pub(super) permission_amount: Option<vir_low::Expression>,
    pub(super) position: vir_low::Position,
    /// Are we folding or unfolding?
    pub(super) is_folding: bool,
}

pub(super) struct MemoryBlockSplitJoiner<'a> {
    pub(super) statements: &'a mut Vec<vir_low::Statement>,
    pub(super) permission_amount: Option<vir_low::Expression>,
    pub(super) position: vir_low::Position,
    /// Are we joining or splitting?
    pub(super) is_joining: bool,
}

// Type aliases to make sure that function signatures fit on a single line for
// easier comparison of implementions since they are very similar.
type R = SpannedEncodingResult<()>;

impl<'a> OwnedUnFolder<'a> {
    fn permission_amount(&self) -> vir_low::Expression {
        if let Some(permission_amount) = &self.permission_amount {
            permission_amount.clone()
        } else {
            vir_low::Expression::full_permission()
        }
    }
}

type PO = (vir_low::Expression, vir_low::Expression);
impl<'a> TypeDeclWalker for OwnedUnFolder<'a> {
    type Parameters = (vir_low::Expression, vir_low::Expression);
    fn before(&mut self, ty: &Type, (place, snapshot): &PO, _: &mut Lowerer) -> R {
        if !self.is_folding {
            self.statements.push(stmtp! {
                self.position =>
                unfold acc(
                    OwnedNonAliased<ty>(
                        [place.clone()], [self.root_address.clone()], [snapshot.clone()]
                    ),
                    [self.permission_amount()]
                )
            });
        }
        Ok(())
    }
    fn after(&mut self, ty: &Type, (place, snapshot): PO, lowerer: &mut Lowerer) -> R {
        if self.is_folding {
            self.statements.push(stmtp! {
                self.position =>
                fold acc(
                    OwnedNonAliased<ty>([place], [self.root_address.clone()], [snapshot]),
                    [self.permission_amount()]
                )
            });
        }
        lowerer.mark_owned_non_aliased_as_unfolded(ty)
    }
    fn walk_field(&mut self, ty: &Type, field: &FieldDecl, p: &PO, lowerer: &mut Lowerer) -> R {
        let (place, snapshot) = p;
        let field_place = lowerer.encode_field_place(ty, field, place.clone(), self.position)?;
        let field_snapshot =
            lowerer.obtain_struct_field_snapshot(ty, field, snapshot.clone(), self.position)?;
        self.walk_type(&field.ty, (field_place, field_snapshot), lowerer)
    }
}

impl<'a> MemoryBlockSplitJoiner<'a> {
    fn permission_amount(&self) -> vir_low::Expression {
        if let Some(permission_amount) = &self.permission_amount {
            permission_amount.clone()
        } else {
            vir_low::Expression::full_permission()
        }
    }
}

type PM = vir_low::Expression;
impl<'a> TypeDeclWalker for MemoryBlockSplitJoiner<'a> {
    const IS_EMPTY_PRIMITIVE: bool = true;
    type Parameters = vir_low::Expression;
    fn before_composite(&mut self, ty: &Type, address: &PM, lowerer: &mut Lowerer) -> R {
        assert!(!lowerer.encoder.is_type_empty(ty)?);
        if !self.is_joining {
            lowerer.encode_memory_block_split_method(ty)?;
            if ty.has_variants() {
                unreachable!("ty: {}", ty);
            } else {
                self.statements.push(stmtp! { self.position =>
                    call memory_block_split<ty>([address.clone()], [self.permission_amount()])
                });
            }
        }
        Ok(())
    }
    fn after_composite(&mut self, ty: &Type, address: PM, lowerer: &mut Lowerer) -> R {
        assert!(!lowerer.encoder.is_type_empty(ty)?);
        if self.is_joining {
            lowerer.encode_memory_block_join_method(ty)?;
            self.statements.push(stmtp! { self.position =>
                call memory_block_join<ty>([address], [self.permission_amount()])
            });
        }
        Ok(())
    }
    fn walk_field(&mut self, ty: &Type, field: &FieldDecl, p: &PM, lowerer: &mut Lowerer) -> R {
        let address = p;
        let field_address =
            lowerer.encode_field_address(ty, field, address.clone(), Default::default())?;
        self.walk_type(&field.ty, field_address, lowerer)
    }
}
