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

pub(in super::super::super::super::super) struct UniqueRefUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>,
    target_slice_len: Option<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx, G> UniqueRefUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    #[allow(clippy::too_many_arguments)]
    pub(in super::super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let mut arguments = vec![place, address, lifetime];
        if let Some(len) = target_slice_len.clone() {
            arguments.push(len);
        }
        let inner = PredicateUseBuilder::new(
            lowerer,
            "UniqueRef",
            context,
            ty,
            generics,
            arguments,
            position,
        )?;
        Ok(Self {
            inner,
            target_slice_len,
        })
    }

    pub(in super::super::super::super::super) fn build(
        self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(self.inner.build())
    }

    pub(in super::super::super::super::super) fn add_lifetime_arguments(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.add_lifetime_arguments()
    }

    pub(in super::super::super::super::super) fn add_const_arguments(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        if self.inner.ty.is_slice() {
            // FIXME
            eprintln!("FIXME!!!");
            // let snapshot_length = self
            //     .inner
            //     .lowerer
            //     .obtain_array_len_snapshot(self.current_snapshot.clone(), self.inner.position)?;
            // let size_type = self.inner.lowerer.size_type_mid()?;
            // let argument = self.inner.lowerer.construct_constant_snapshot(
            //     &size_type,
            //     snapshot_length,
            //     self.inner.position,
            // )?;
            // self.inner.arguments.push(argument);
        }
        self.inner.add_const_arguments()
    }

    pub(in super::super::super::super::super) fn set_maybe_permission_amount(
        &mut self,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        self.inner.set_maybe_permission_amount(permission_amount)
    }
}
