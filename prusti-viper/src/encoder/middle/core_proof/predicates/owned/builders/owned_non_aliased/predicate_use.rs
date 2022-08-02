use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, lowerer::Lowerer,
        predicates::owned::builders::common::predicate_use::PredicateUseBuilder,
    },
};
use vir_crate::{
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
        root_address: vir_low::Expression,
        snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<Self> {
        let inner = PredicateUseBuilder::new(
            lowerer,
            "OwnedNonAliased",
            context,
            ty,
            generics,
            vec![place, root_address, snapshot],
            Default::default(),
        )?;
        Ok(Self { inner })
    }

    pub(in super::super::super::super::super) fn build(self) -> vir_low::Expression {
        self.inner.build()
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
