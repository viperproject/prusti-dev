use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::calls::interface::CallContext, const_generics::ConstGenericsInterface,
        lifetimes::LifetimesInterface, lowerer::Lowerer,
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

pub(in super::super::super) struct BuiltinMethodCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) context: CallContext,
    pub(in super::super) method_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) generics: &'l G,
    pub(in super::super) arguments: Vec<vir_low::Expression>,
    pub(in super::super) targets: Vec<vir_low::Expression>,
    pub(in super::super) guard: Option<vir_low::Expression>,
    pub(in super::super) position: vir_low::Position,
}

impl<'l, 'p, 'v, 'tcx, G> BuiltinMethodCallBuilder<'l, 'p, 'v, 'tcx, G>
where
    G: WithLifetimes + WithConstArguments,
{
    pub(in super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        context: CallContext,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        generics: &'l G,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            context,
            method_name,
            ty,
            generics,
            arguments: Vec::new(),
            targets: Vec::new(),
            guard: None,
            position,
            lowerer,
        })
    }

    pub(in super::super::super) fn build(self) -> vir_low::Statement {
        let method_call = vir_low::Statement::method_call(
            format!("{}${}", self.method_name, self.ty.get_identifier()),
            self.arguments,
            self.targets,
            self.position,
        );
        if let Some(guard) = self.guard {
            vir_low::Statement::conditional_no_pos(guard, vec![method_call], Vec::new())
        } else {
            method_call
        }
    }

    pub(in super::super::super) fn add_argument(&mut self, argument: vir_low::Expression) {
        self.arguments.push(argument);
    }

    pub(in super::super::super) fn add_full_permission_argument(&mut self) {
        self.add_argument(vir_low::Expression::full_permission());
    }

    pub(in super::super::super) fn add_lifetime_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.arguments.extend(
            self.lowerer
                .create_lifetime_arguments(self.context, self.generics)?,
        );
        Ok(())
    }

    pub(in super::super::super) fn add_const_arguments(&mut self) -> SpannedEncodingResult<()> {
        self.arguments.extend(
            self.lowerer
                .create_const_arguments(self.context, self.generics)?,
        );
        Ok(())
    }

    pub(in super::super::super) fn set_guard(&mut self, guard: vir_low::Expression) {
        assert!(self.guard.is_none(), "guard is alread set");
        self.guard = Some(guard);
    }

    pub(in super::super::super) fn set_maybe_guard(&mut self, guard: Option<vir_low::Expression>) {
        if let Some(guard) = guard {
            self.set_guard(guard);
        }
    }
}
