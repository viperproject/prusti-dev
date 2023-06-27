use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        snapshots::{IntoPureSnapshot, IntoSnapshot},
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle as vir_mid,
    middle::operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
};

pub(in super::super) struct FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) function_name: &'l str,
    pub(in super::super) context: CallContext,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) generics: &'l G,
    pub(in super::super) arguments: Vec<vir_low::Expression>,
    pub(in super::super) position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx, G> FunctionCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        function_name: &'l str,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            lowerer,
            function_name,
            context,
            ty,
            generics,
            arguments,
            position,
        })
    }

    pub(in super::super) fn build(self) -> SpannedEncodingResult<vir_low::Expression> {
        let return_type = self.ty.to_snapshot(self.lowerer)?;
        let call = vir_low::Expression::function_call(
            format!("{}${}", self.function_name, self.ty.get_identifier()),
            self.arguments,
            return_type,
        );
        Ok(call.set_default_position(self.position))
    }

    pub(in super::super) fn add_lifetime_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.arguments.extend(
            self.lowerer
                .create_lifetime_arguments(self.context, self.generics)?,
        );
        Ok(())
    }

    pub(in super::super) fn add_const_arguments(&mut self) -> SpannedEncodingResult<()> {
        // FIXME: remove code duplication with other add_const_arguments methods
        for argument in self.generics.get_const_arguments() {
            self.arguments
                .push(argument.to_pure_snapshot(self.lowerer)?);
        }
        Ok(())
    }
}
