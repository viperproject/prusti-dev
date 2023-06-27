use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, lowerer::Lowerer,
        predicates::owned::builders::common::function_use::FunctionCallBuilder,
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super::super::super) struct OwnedNonAliasedSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>,
}

impl<'l, 'p, 'v, 'tcx, G> OwnedNonAliasedSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
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
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let arguments = vec![place, address];
        let inner = FunctionCallBuilder::new(
            lowerer,
            "snap_owned_non_aliased",
            context,
            ty,
            generics,
            arguments,
            position,
        )?;
        Ok(Self { inner })
    }

    pub(in super::super::super::super::super) fn build(
        self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.build()
    }

    pub(in super::super::super::super::super) fn add_custom_argument(
        &mut self,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.inner.arguments.push(argument);
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
}
