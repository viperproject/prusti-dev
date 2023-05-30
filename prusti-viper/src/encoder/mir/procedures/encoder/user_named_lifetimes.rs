use super::ProcedureEncoder;
use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use std::collections::BTreeMap;
use vir_crate::high::{self as vir_high, visitors::ExpressionFallibleFolder};

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn resolve_lifetimes(
        &mut self,
        expression: vir_high::Expression,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let mut resolver = Resolver {
            user_named_lifetimes: &self.user_named_lifetimes,
        };
        resolver.fallible_fold_expression(expression)
    }
}

struct Resolver<'a> {
    user_named_lifetimes: &'a BTreeMap<String, vir_high::ty::LifetimeConst>,
}

impl<'a> ExpressionFallibleFolder for Resolver<'a> {
    type Error = SpannedEncodingError;

    fn fallible_fold_builtin_func_app_enum(
        &mut self,
        mut builtin_func_app: vir_high::BuiltinFuncApp,
    ) -> Result<vir_high::Expression, Self::Error> {
        let result = match builtin_func_app.function {
            vir_high::BuiltinFunc::BuildingUniqueRefPredicate => {
                let place = builtin_func_app.arguments.pop().unwrap();
                let lifetime = builtin_func_app.arguments.pop().unwrap();
                let vir_high::Expression::Constant(vir_high::Constant {
                    value: vir_high::expression::ConstantValue::String(lifetime),
                    ..
                }) = lifetime else {
                    unreachable!("lifetime: {lifetime:?}")
                };
                let lifetime = self.user_named_lifetimes.get(&lifetime).unwrap().clone();
                let position = builtin_func_app.position;
                vir_high::Expression::acc_predicate(
                    vir_high::Predicate::unique_ref(lifetime, place, position),
                    position,
                )
            }
            vir_high::BuiltinFunc::BuildingFracRefPredicate => {
                let place = builtin_func_app.arguments.pop().unwrap();
                let lifetime = builtin_func_app.arguments.pop().unwrap();
                let vir_high::Expression::Constant(vir_high::Constant {
                    value: vir_high::expression::ConstantValue::String(lifetime),
                    ..
                }) = lifetime else {
                    unreachable!("lifetime: {lifetime:?}")
                };
                let lifetime = self.user_named_lifetimes.get(&lifetime).unwrap().clone();
                let position = builtin_func_app.position;
                vir_high::Expression::acc_predicate(
                    vir_high::Predicate::frac_ref(lifetime, place, position),
                    position,
                )
            }
            _ => vir_high::Expression::BuiltinFuncApp(builtin_func_app),
        };
        Ok(result)
    }
}
