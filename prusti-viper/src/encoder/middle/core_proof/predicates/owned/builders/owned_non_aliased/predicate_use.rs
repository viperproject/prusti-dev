use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::Lowerer,
        predicates::{
            owned::builders::common::predicate_use::PredicateUseBuilder, PredicatesOwnedInterface,
        },
    },
};
use prusti_common::config;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super::super::super) struct OwnedNonAliasedUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>,
    snapshot: Option<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx, G> OwnedNonAliasedUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<Self> {
        let arguments = vec![place, address];
        let inner = PredicateUseBuilder::new(
            lowerer,
            "OwnedNonAliased",
            context,
            ty,
            generics,
            arguments,
            position,
        )?;
        Ok(Self {
            inner,
            snapshot: None,
        })
    }

    pub(in super::super::super::super::super) fn build(
        mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let expression = if let Some(snapshot) = self.snapshot.take() {
            let snap_call = self.inner.lowerer.owned_non_aliased_snap(
                self.inner.context,
                self.inner.ty,
                self.inner.generics,
                self.inner.arguments[0].clone(),
                self.inner.arguments[1].clone(),
                self.inner.position,
            )?;
            vir_low::Expression::and(
                self.inner.build(),
                vir_low::Expression::equals(snapshot, snap_call),
            )
        } else {
            self.inner.build()
        };
        Ok(expression)
    }

    pub(in super::super::super::super::super) fn add_snapshot_argument(
        &mut self,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        if config::use_snapshot_parameters_in_predicates() {
            self.inner.arguments.push(snapshot);
        } else {
            self.snapshot = Some(snapshot);
        }
        Ok(())
    }

    pub(in super::super::super::super::super) fn add_lifetime_arguments(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_lifetime_arguments()
    }

    pub(in super::super::super::super::super) fn add_const_arguments(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_const_arguments()
    }

    pub(in super::super::super::super::super) fn add_custom_argument(
        &mut self,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.inner.arguments.push(argument);
        Ok(())
    }

    pub(in super::super::super::super::super) fn set_maybe_permission_amount(
        &mut self,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        self.inner.set_maybe_permission_amount(permission_amount)
    }
}
