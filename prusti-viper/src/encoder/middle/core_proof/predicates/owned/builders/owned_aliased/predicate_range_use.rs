use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lowerer::{DomainsLowererInterface, Lowerer},
        pointers::PointersInterface,
        predicates::{
            owned::builders::common::predicate_use::PredicateUseBuilder, PredicatesOwnedInterface,
        },
        snapshots::{SnapshotValidityInterface, SnapshotValuesInterface},
        type_layouts::TypeLayoutsInterface,
    },
};
use prusti_common::config;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, QuantifierHelpers},
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super::super::super) struct OwnedAliasedRangeUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    context: CallContext,
    ty: &'l vir_mid::Type,
    generics: &'l G,
    address: vir_low::Expression,
    start_index: vir_low::Expression,
    end_index: vir_low::Expression,
    permission_amount: Option<vir_low::Expression>,
    position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx, G> OwnedAliasedRangeUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        address: vir_low::Expression,
        start_index: vir_low::Expression,
        end_index: vir_low::Expression,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            lowerer,
            context,
            ty,
            generics,
            address,
            start_index,
            end_index,
            permission_amount,
            position: Default::default(),
        })
    }

    pub(in super::super::super::super::super) fn build(
        self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::macros::*;
        let size_type = self.lowerer.size_type_mid()?;
        var_decls! {
            index: Int
        }
        let vir_mid::Type::Pointer(ty) = self.ty else {
            unreachable!()
        };
        let initial_address = self
            .lowerer
            .pointer_address(self.ty, self.address, self.position)?;
        let vir_mid::Type::Pointer(pointer_type) = self.ty else {
            unreachable!()
        };
        let size = self
            .lowerer
            .encode_type_size_expression2(&*pointer_type.target_type, &*pointer_type.target_type)?;
        let element_address = self.lowerer.address_offset(
            size,
            initial_address,
            index.clone().into(),
            self.position,
        )?;
        let predicate = self.lowerer.owned_aliased(
            self.context,
            &ty.target_type,
            self.generics,
            element_address.clone(),
            self.permission_amount,
        )?;
        let start_index =
            self.lowerer
                .obtain_constant_value(&size_type, self.start_index, self.position)?;
        let end_index =
            self.lowerer
                .obtain_constant_value(&size_type, self.end_index, self.position)?;
        let body = expr!(
            (([start_index] <= index) && (index < [end_index])) ==> [predicate]
        );
        let expression = vir_low::Expression::forall(
            vec![index],
            vec![vir_low::Trigger::new(vec![element_address])],
            body,
        );
        Ok(expression)
    }
}
