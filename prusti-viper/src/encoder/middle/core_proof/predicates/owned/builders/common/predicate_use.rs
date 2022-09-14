use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext, const_generics::ConstGenericsInterface,
        lifetimes::LifetimesInterface, lowerer::Lowerer,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle as vir_mid,
    middle::operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
};

pub(in super::super) struct PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) predicate_name: &'l str,
    pub(in super::super) context: CallContext,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) generics: &'l G,
    pub(in super::super) arguments: Vec<vir_low::Expression>,
    pub(in super::super) permission_amount: Option<vir_low::Expression>,
    pub(in super::super) position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx, G> PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        predicate_name: &'l str,
        context: CallContext,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        arguments: Vec<vir_low::Expression>,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            lowerer,
            predicate_name,
            context,
            ty,
            generics,
            arguments,
            permission_amount: None,
            position,
        })
    }

    pub(in super::super) fn build(self) -> vir_low::Expression {
        vir_low::Expression::predicate_access_predicate(
            self.predicate_name(),
            self.arguments,
            self.permission_amount
                .unwrap_or_else(vir_low::Expression::full_permission),
            self.position,
        )
    }

    pub(in super::super) fn predicate_name(&self) -> String {
        format!("{}${}", self.predicate_name, self.ty.get_identifier())
    }

    pub(in super::super) fn add_lifetime_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.arguments.extend(
            self.lowerer
                .create_lifetime_arguments(self.context, self.generics)?,
        );
        Ok(())
    }

    pub(in super::super) fn add_const_arguments(&mut self) -> SpannedEncodingResult<()> {
        // // FIXME: remove code duplication with other add_const_arguments methods
        // for argument in self.generics.get_const_arguments() {
        //     self.arguments
        //         .push(argument.to_pure_snapshot(self.lowerer)?);
        // }
        self.arguments.extend(
            self.lowerer
                .create_const_arguments(self.context, self.generics)?,
        );
        Ok(())
    }

    pub(in super::super) fn set_maybe_permission_amount(
        &mut self,
        permission_amount: Option<vir_low::Expression>,
    ) -> SpannedEncodingResult<()> {
        if let Some(permission_amount) = permission_amount {
            assert!(
                self.permission_amount.is_none(),
                "The permission amount is already set"
            );
            self.permission_amount = Some(permission_amount);
        }
        Ok(())
    }
}
