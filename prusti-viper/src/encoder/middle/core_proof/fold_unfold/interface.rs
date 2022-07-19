use super::helpers::{MemoryBlockSplitJoiner, OwnedUnFolder};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{lowerer::Lowerer, utils::type_decl_encoder::TypeDeclWalker},
};

use vir_crate::{low as vir_low, middle as vir_mid};

pub(in super::super) trait FoldUnfoldInterface {
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    #[allow(clippy::too_many_arguments)]
    fn encode_fully_fold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    #[allow(clippy::too_many_arguments)]
    fn encode_fully_unfold_owned_non_aliased(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        place: vir_low::Expression,
        root_address: &vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn encode_fully_split_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()>;
    #[allow(clippy::ptr_arg)] // Clippy false positive.
    fn encode_fully_join_memory_block(
        &mut self,
        statements: &mut Vec<vir_low::Statement>,
        ty: &vir_mid::Type,
        address: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
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
        permission_amount: Option<vir_low::Expression>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut folder = OwnedUnFolder {
            statements,
            root_address,
            permission_amount,
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
        permission_amount: Option<vir_low::Expression>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut unfolder = OwnedUnFolder {
            statements,
            root_address,
            permission_amount,
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
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut spliter = MemoryBlockSplitJoiner {
            statements,
            permission_amount,
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
        permission_amount: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let mut joiner = MemoryBlockSplitJoiner {
            statements,
            permission_amount,
            position,
            is_joining: true,
        };
        joiner.walk_type(ty, address, self)
    }
}
