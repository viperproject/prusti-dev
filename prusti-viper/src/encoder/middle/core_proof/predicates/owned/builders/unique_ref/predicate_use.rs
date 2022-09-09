use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, lowerer::Lowerer,
        predicates::owned::builders::common::predicate_use::PredicateUseBuilder,
        snapshots::SnapshotValuesInterface, type_layouts::TypeLayoutsInterface,
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
    current_snapshot: vir_low::Expression,
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
        root_address: vir_low::Expression,
        current_snapshot: vir_low::Expression,
        final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<Self> {
        let inner = PredicateUseBuilder::new(
            lowerer,
            "UniqueRef2",
            context,
            ty,
            generics,
            vec![
                place,
                root_address,
                current_snapshot.clone(),
                final_snapshot,
                lifetime,
            ],
            Default::default(),
        )?;
        Ok(Self {
            inner,
            current_snapshot,
        })
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
        if self.inner.ty.is_slice() {
            let snapshot_length = self
                .inner
                .lowerer
                .obtain_array_len_snapshot(self.current_snapshot.clone(), self.inner.position)?;
            let size_type = self.inner.lowerer.size_type_mid()?;
            let argument = self.inner.lowerer.construct_constant_snapshot(
                &size_type,
                snapshot_length,
                self.inner.position,
            )?;
            self.inner.arguments.push(argument);
        }
        self.inner.add_const_arguments()
    }
}
