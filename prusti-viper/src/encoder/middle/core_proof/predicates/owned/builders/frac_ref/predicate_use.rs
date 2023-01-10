use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::Lowerer,
        predicates::{
            owned::builders::common::predicate_use::PredicateUseBuilder, PredicatesOwnedInterface,
        },
        snapshots::SnapshotValuesInterface,
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super::super::super) struct FracRefUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>,
    current_snapshot: Option<vir_low::Expression>,
}

impl<'l, 'p, 'v, 'tcx, G> FracRefUseBuilder<'l, 'p, 'v, 'tcx, G>
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
        // current_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
    ) -> SpannedEncodingResult<Self> {
        let inner = PredicateUseBuilder::new(
            lowerer,
            "FracRef2",
            context,
            ty,
            generics,
            vec![
                place,
                root_address, // current_snapshot.clone(),
                lifetime,
            ],
            Default::default(),
        )?;
        Ok(Self {
            inner,
            current_snapshot: None,
        })
    }

    pub(in super::super::super::super::super) fn build(
        mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let expression = if let Some(snapshot) = self.current_snapshot.take() {
            let TODO_target_slice_len = None;
            let snap_call = self.inner.lowerer.frac_ref_snap(
                self.inner.context,
                self.inner.ty,
                self.inner.generics,
                self.inner.arguments[0].clone(),
                self.inner.arguments[1].clone(),
                self.inner.arguments[2].clone(),
                TODO_target_slice_len,
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
        self.current_snapshot = Some(snapshot);
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
        if self.inner.ty.is_slice() {
            unimplemented!();
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
}
