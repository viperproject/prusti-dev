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

pub(in super::super::super::super::super) struct UniqueRefUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>,
    current_snapshot: Option<vir_low::Expression>,
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
        root_address: vir_low::Expression,
        // current_snapshot: vir_low::Expression,
        // final_snapshot: vir_low::Expression,
        lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<Self> {
        let mut arguments = vec![
            place,
            root_address,
            // current_snapshot.clone(),
            lifetime,
            // final_snapshot,
        ];
        if let Some(len) = target_slice_len.clone() {
            arguments.push(len);
        }
        let inner = PredicateUseBuilder::new(
            lowerer,
            "UniqueRef2",
            context,
            ty,
            generics,
            arguments,
            Default::default(),
        )?;
        Ok(Self {
            inner,
            target_slice_len,
            current_snapshot: None,
            // current_snapshot,
        })
    }

    pub(in super::super::super::super::super) fn build(
        mut self,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let expression = if let Some(current_snapshot) = self.current_snapshot.take() {
            let snap_current_call = self.inner.lowerer.unique_ref_snap(
                self.inner.context,
                self.inner.ty,
                self.inner.generics,
                self.inner.arguments[0].clone(),
                self.inner.arguments[1].clone(),
                self.inner.arguments[2].clone(),
                self.target_slice_len.clone(),
                false,
            )?;
            // let snap_final_call = self.inner.lowerer.unique_ref_snap(
            //     self.inner.context,
            //     self.inner.ty,
            //     self.inner.generics,
            //     self.inner.arguments[0].clone(),
            //     self.inner.arguments[1].clone(),
            //     self.inner.arguments[2].clone(),
            //     self.target_slice_len,
            //     true,
            // )?;
            vir_low::Expression::and(
                self.inner.build(),
                // vir_low::Expression::and(
                vir_low::Expression::equals(current_snapshot, snap_current_call),
                // vir_low::Expression::equals(final_snapshot, snap_final_call),
                // ),
            )
        } else {
            self.inner.build()
        };
        Ok(expression)
    }

    pub(in super::super::super::super::super) fn add_current_snapshot_argument(
        &mut self,
        current_snapshot: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        // if config::use_snapshot_parameters_in_predicates() {
        //     self.inner.arguments.push(current_snapshot);
        //     self.inner.arguments.push(final_snapshot);
        // } else {
        self.current_snapshot = Some(current_snapshot);
        // }
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
}
