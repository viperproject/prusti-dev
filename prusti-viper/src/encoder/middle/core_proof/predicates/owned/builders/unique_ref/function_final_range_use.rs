use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, function_gas::FunctionGasInterface, lowerer::Lowerer,
        predicates::owned::builders::common::function_use::FunctionCallBuilder,
        snapshots::IntoSnapshot,
    },
};
use prusti_common::config;
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{
        self as vir_mid,
        operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
    },
};

pub(in super::super::super::super::super) struct UniqueRefFinalRangeSnapCallBuilder<
    'l,
    'p,
    'v,
    'tcx,
    G,
> where
    G: WithLifetimes + WithConstArguments,
{
    inner: FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>,
}

impl<'l, 'p, 'v, 'tcx, G> UniqueRefFinalRangeSnapCallBuilder<'l, 'p, 'v, 'tcx, G>
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
        reference_lifetime: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        let arguments = vec![address, start_index, end_index, reference_lifetime];
        let inner = FunctionCallBuilder::new(
            lowerer,
            "snap_unique_ref_final_range_aliased",
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
        let vir_mid::Type::Pointer(pointer_type) = self.inner.ty else {
            unreachable!("{} must be a pointer type", self.inner.ty);
        };
        let element_type = pointer_type.target_type.to_snapshot(self.inner.lowerer)?;
        let return_type = vir_low::Type::seq(element_type);
        let gas_amount = self
            .inner
            .lowerer
            .function_gas_constant(config::function_gas_amount())?;
        let mut arguments = self.inner.arguments;
        arguments.push(gas_amount);
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

    // pub(in super::super::super::super::super) fn add_custom_argument(
    //     &mut self,
    //     argument: vir_low::Expression,
    // ) -> SpannedEncodingResult<()> {
    //     self.inner.arguments.push(argument);
    //     Ok(())
    // }

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
