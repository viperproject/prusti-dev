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

pub(in super::super::super) struct UniqueRefCurrentSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>,
}

impl<'l, 'p, 'v, 'tcx, G> UniqueRefCurrentSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        place: vir_low::Expression,
        root_address: vir_low::Expression,
        reference_lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let mut arguments = vec![place, root_address, reference_lifetime];
        if let Some(len) = target_slice_len {
            arguments.push(len);
        }
        let name = "snap_current_unique_ref";
        let inner =
            FunctionCallBuilder::new(lowerer, name, context, ty, generics, arguments, position)?;
        Ok(Self { inner })
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::Expression> {
        self.inner.build()
    }

    pub(in super::super::super) fn add_lifetime_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_lifetime_arguments()
    }

    pub(in super::super::super) fn add_const_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_const_arguments()
    }
}
