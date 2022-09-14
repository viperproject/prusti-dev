use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::custom_heap_encoding::heap_encoder::HeapEncoder,
};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

pub(in super::super) trait PermissionMaskKind {}
pub(in super::super) struct PermissionMaskKindAliasedFractionalBoundedPerm {}
impl PermissionMaskKind for PermissionMaskKindAliasedFractionalBoundedPerm {}
pub(in super::super) struct PermissionMaskKindAliasedBool {}
impl PermissionMaskKind for PermissionMaskKindAliasedBool {}

pub(in super::super) struct PermissionMaskOperations<Kind: PermissionMaskKind> {
    _kind: std::marker::PhantomData<Kind>,
    old_permission_mask_version: vir_low::Expression,
    new_permission_mask_version: vir_low::Expression,
    perm_old: vir_low::Expression,
    perm_new: vir_low::Expression,
}

impl<K: PermissionMaskKind> PermissionMaskOperations<K> {
    pub(in super::super) fn new<'p, 'v: 'p, 'tcx: 'v>(
        heap_encoder: &mut HeapEncoder<'p, 'v, 'tcx>,
        statements: &mut Vec<vir_low::Statement>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        expression_evaluation_state_label: Option<String>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let old_permission_mask_version =
            heap_encoder.get_current_permission_mask_for(&predicate.name)?;
        let new_permission_mask_version =
            heap_encoder.get_new_permission_mask_for(&predicate.name, position)?;
        let perm_old = heap_encoder.permission_mask_call_for_predicate_use(
            statements,
            predicate,
            old_permission_mask_version.clone(),
            expression_evaluation_state_label.clone(),
            position,
        )?;
        let perm_new = heap_encoder.permission_mask_call_for_predicate_use(
            statements,
            predicate,
            new_permission_mask_version.clone(),
            expression_evaluation_state_label,
            position,
        )?;
        Ok(Self {
            _kind: std::marker::PhantomData,
            old_permission_mask_version,
            new_permission_mask_version,
            perm_old,
            perm_new,
        })
    }

    pub(in super::super) fn perm_new(&self) -> vir_low::Expression {
        self.perm_new.clone()
    }

    pub(in super::super) fn old_permission_mask_version(&self) -> vir_low::Expression {
        self.old_permission_mask_version.clone()
    }

    pub(in super::super) fn new_permission_mask_version(&self) -> vir_low::Expression {
        self.new_permission_mask_version.clone()
    }
}

pub(in super::super) trait TPermissionMaskOperations {
    fn perm_old_greater_equals(
        &self,
        permission_amount: &vir_low::Expression,
    ) -> vir_low::Expression;

    fn perm_old_positive(&self) -> vir_low::Expression;

    fn perm_old_sub(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression;

    fn perm_old_add(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression;

    fn perm_old_equal_none(&self) -> vir_low::Expression;

    fn can_assume_old_permission_is_none(&self, permission_amount: &vir_low::Expression) -> bool;
}

impl TPermissionMaskOperations
    for PermissionMaskOperations<PermissionMaskKindAliasedFractionalBoundedPerm>
{
    fn perm_old_greater_equals(
        &self,
        permission_amount: &vir_low::Expression,
    ) -> vir_low::Expression {
        vir_low::Expression::greater_equals(self.perm_old.clone(), permission_amount.clone())
    }

    fn perm_old_positive(&self) -> vir_low::Expression {
        vir_low::Expression::greater_equals(
            self.perm_old.clone(),
            vir_low::Expression::no_permission(),
        )
    }

    fn perm_old_sub(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression {
        if permission_amount.is_full_permission() {
            vir_low::Expression::no_permission()
        } else {
            vir_low::Expression::perm_binary_op_no_pos(
                vir_low::ast::expression::PermBinaryOpKind::Sub,
                self.perm_old.clone(),
                permission_amount.clone(),
            )
        }
    }

    fn perm_old_add(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression {
        if permission_amount.is_full_permission() {
            vir_low::Expression::full_permission()
        } else {
            vir_low::Expression::perm_binary_op_no_pos(
                vir_low::ast::expression::PermBinaryOpKind::Add,
                self.perm_old.clone(),
                permission_amount.clone(),
            )
        }
    }

    fn perm_old_equal_none(&self) -> vir_low::Expression {
        vir_low::Expression::equals(self.perm_old.clone(), vir_low::Expression::no_permission())
    }

    fn can_assume_old_permission_is_none(&self, permission_amount: &vir_low::Expression) -> bool {
        permission_amount.is_full_permission()
    }
}

impl TPermissionMaskOperations for PermissionMaskOperations<PermissionMaskKindAliasedBool> {
    fn perm_old_greater_equals(
        &self,
        permission_amount: &vir_low::Expression,
    ) -> vir_low::Expression {
        assert!(permission_amount.is_full_permission());
        self.perm_old.clone()
    }

    fn perm_old_positive(&self) -> vir_low::Expression {
        self.perm_old.clone()
    }

    fn perm_old_sub(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression {
        assert!(permission_amount.is_full_permission());
        false.into()
    }

    fn perm_old_add(&self, permission_amount: &vir_low::Expression) -> vir_low::Expression {
        assert!(permission_amount.is_full_permission());
        true.into()
    }

    fn perm_old_equal_none(&self) -> vir_low::Expression {
        vir_low::Expression::equals(self.perm_old.clone(), false.into())
    }

    fn can_assume_old_permission_is_none(&self, _: &vir_low::Expression) -> bool {
        true
    }
}
