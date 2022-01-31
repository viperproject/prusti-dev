use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface, lowerer::Lowerer, snapshots::SnapshotsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use vir_crate::{low as vir_low, middle as vir_mid};
use vir_low::macros::*;
use vir_mid::{FieldDecl, Type};

pub(super) struct ToAddressWriter<'a> {
    pub(super) statements: &'a mut Vec<vir_low::Statement>,
    pub(super) position: vir_low::Position,
}

type R = SpannedEncodingResult<()>;

type PW = (vir_low::Expression, vir_low::Expression);
impl<'a> TypeDeclWalker for ToAddressWriter<'a> {
    type Parameters = (vir_low::Expression, vir_low::Expression);
    fn walk_primitive(&mut self, ty: &Type, (address, value): &PW, _lowerer: &mut Lowerer) -> R {
        self.statements.push(stmtp! { self.position =>
            call write_address<ty>([address.clone()], [value.clone()])
        });
        Ok(())
    }
    fn walk_field(&mut self, ty: &Type, field: &FieldDecl, p: &PW, lowerer: &mut Lowerer) -> R {
        let (address, value) = p;
        let field_address =
            lowerer.encode_field_address(ty, field, address.clone(), Default::default())?;
        let field_value =
            lowerer.encode_field_snapshot(ty, field, value.clone(), Default::default())?;
        self.walk_type(&field.ty, (field_address, field_value), lowerer)
    }
}
