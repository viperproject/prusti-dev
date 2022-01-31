use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, builtin_methods::BuiltinMethodsInterface, lowerer::Lowerer,
        places::PlacesInterface, predicates_owned::PredicatesOwnedInterface,
        snapshots::SnapshotsInterface, utils::type_decl_encoder::TypeDeclWalker,
    },
};
use vir_crate::{low as vir_low, middle as vir_mid};
use vir_low::macros::*;
use vir_mid::{FieldDecl, Type};

pub(super) struct OwnedUnFolder<'a> {
    pub(super) statements: &'a mut Vec<vir_low::Statement>,
    pub(super) root_address: &'a vir_low::Expression,
    pub(super) position: vir_low::Position,
    /// Are we folding or unfolding?
    pub(super) is_folding: bool,
}

pub(super) struct MemoryBlockSplitJoiner<'a> {
    pub(super) statements: &'a mut Vec<vir_low::Statement>,
    pub(super) position: vir_low::Position,
    /// Are we joining or splitting?
    pub(super) is_joining: bool,
}

// Type aliases to make sure that function signatures fit on a single line for
// easier comparison of implementions since they are very similar.
type R = SpannedEncodingResult<()>;

type PO = (vir_low::Expression, vir_low::Expression);
impl<'a> TypeDeclWalker for OwnedUnFolder<'a> {
    type Parameters = (vir_low::Expression, vir_low::Expression);
    fn before(&mut self, ty: &Type, (place, snapshot): &PO, _: &mut Lowerer) -> R {
        if !self.is_folding {
            self.statements.push(stmtp! {
                self.position =>
                unfold OwnedNonAliased<ty>([place.clone()], [self.root_address.clone()], [snapshot.clone()])
            });
        }
        Ok(())
    }
    fn after(&mut self, ty: &Type, (place, snapshot): PO, lowerer: &mut Lowerer) -> R {
        if self.is_folding {
            self.statements.push(stmtp! {
                self.position =>
                fold OwnedNonAliased<ty>([place], [self.root_address.clone()], [snapshot])
            });
        }
        lowerer.mark_owned_non_aliased_as_unfolded(ty)
    }
    fn walk_field(&mut self, ty: &Type, field: &FieldDecl, p: &PO, lowerer: &mut Lowerer) -> R {
        let (place, snapshot) = p;
        let field_place = lowerer.encode_field_place(ty, field, place.clone(), self.position)?;
        let field_snapshot =
            lowerer.encode_field_snapshot(ty, field, snapshot.clone(), self.position)?;
        self.walk_type(&field.ty, (field_place, field_snapshot), lowerer)
    }
}

type PM = vir_low::Expression;
impl<'a> TypeDeclWalker for MemoryBlockSplitJoiner<'a> {
    type Parameters = vir_low::Expression;
    fn before_composite(&mut self, ty: &Type, address: &PM, lowerer: &mut Lowerer) -> R {
        if !self.is_joining {
            lowerer.encode_memory_block_split_method(ty)?;
            self.statements.push(stmtp! {
                self.position => call memory_block_split<ty>([address.clone()])
            });
        }
        Ok(())
    }
    fn after_composite(&mut self, ty: &Type, address: PM, lowerer: &mut Lowerer) -> R {
        if self.is_joining {
            lowerer.encode_memory_block_join_method(ty)?;
            self.statements.push(stmtp! {
                self.position => call memory_block_join<ty>([address])
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
