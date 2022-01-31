use super::helpers::{MemoryBlockSplitJoiner, OwnedUnFolder};
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface, compute_address::ComputeAddressInterface,
        into_low::IntoLowInterface, lowerer::Lowerer, places::PlacesInterface,
        predicates_owned::PredicatesOwnedInterface, snapshots::SnapshotsInterface,
        utils::type_decl_encoder::TypeDeclWalker,
    },
};
use std::borrow::Cow;
use vir_crate::{common::identifier::WithIdentifier, low as vir_low, middle as vir_mid};

pub(in super::super) trait FoldUnfoldInterface {
    fn encode_fully_fold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_fully_unfold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_fully_split_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    fn encode_fully_join_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
}

impl<'p, 'v: 'p, 'tcx: 'v> FoldUnfoldInterface for Lowerer<'p, 'v, 'tcx> {
    fn encode_fully_fold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut folder = OwnedUnFolder {
            statements,
            root_address,
            position,
            is_folding: true,
        };
        folder.walk_type(ty, (place, snapshot), self)
    }
    fn encode_fully_unfold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut unfolder = OwnedUnFolder {
            statements,
            root_address,
            position,
            is_folding: false,
        };
        unfolder.walk_type(ty, (place, snapshot), self)
    }
    fn encode_fully_split_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut spliter = MemoryBlockSplitJoiner {
            statements,
            position,
            is_joining: false,
        };
        spliter.walk_type(ty, address, self)
    }
    fn encode_fully_join_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut joiner = MemoryBlockSplitJoiner {
            statements,
            position,
            is_joining: true,
        };
        joiner.walk_type(ty, address, self)
    }
}
