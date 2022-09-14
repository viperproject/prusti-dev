use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, function_gas::FunctionGasInterface, lowerer::Lowerer,
        predicates::owned::builders::common::function_use::FunctionCallBuilder,
        snapshots::IntoSnapshot,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super) struct UniqueRefFinalSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    inner: FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>,
    gas_amount: vir_low::Expression,
}

impl<'l, 'p, 'v, 'tcx, G> UniqueRefFinalSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        place: vir_low::Expression,
        address: vir_low::Expression,
        reference_lifetime: vir_low::Expression,
        target_slice_len: Option<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let mut arguments = vec![place, address, reference_lifetime];
        if let Some(len) = target_slice_len {
            arguments.push(len);
        }
        let name = "snap_final_unique_ref";
        let gas_amount = lowerer.function_gas_constant(2)?;
        let inner =
            FunctionCallBuilder::new(lowerer, name, context, ty, generics, arguments, position)?;
        Ok(Self { inner, gas_amount })
    }

    pub(in super::super::super) fn build(self) -> SpannedEncodingResult<vir_low::Expression> {
        let return_type = self.inner.ty.to_snapshot(self.inner.lowerer)?;
        let mut arguments = self.inner.arguments;
        arguments.push(self.gas_amount);
        let call = vir_low::Expression::domain_function_call(
            "UniqueRefSnapFunctions",
            format!(
                "{}${}",
                self.inner.function_name,
                self.inner.ty.get_identifier()
            ),
            arguments,
            return_type,
        );
        Ok(call.set_default_position(self.inner.position))
    }

    pub(in super::super::super) fn add_lifetime_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_lifetime_arguments()
    }

    pub(in super::super::super) fn add_const_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.inner.add_const_arguments()
    }

    pub(in super::super::super) fn set_gas_amount(
        &mut self,
        new_gas_amount: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.gas_amount = new_gas_amount;
        Ok(())
    }
}
