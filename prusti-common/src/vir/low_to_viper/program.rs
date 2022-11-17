use super::{Context, ToViper};
use viper::{self, AstFactory};
use vir::low::program::Program;

impl<'v> ToViper<'v, viper::Program<'v>> for Program {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Program<'v> {
        let Program {
            name: _,
            check_mode: _,
            domains,
            procedures,
            predicates,
            functions,
            methods,
        } = self;
        let viper_domains: Vec<_> = domains
            .iter()
            .map(|domain| domain.to_viper(context, ast))
            .collect();
        let viper_methods: Vec<_> = procedures
            .iter()
            .map(|procedure| procedure.to_viper(context, ast))
            .chain(methods.iter().map(|method| method.to_viper(context, ast)))
            .collect();
        let viper_predicates: Vec<_> = predicates
            .iter()
            .map(|predicate| predicate.to_viper(context, ast))
            .collect();
        // FIXME: These should be domain functions:
        let viper_functions: Vec<_> = functions
            .iter()
            .map(|function| function.to_viper(context, ast))
            .collect();
        ast.program(
            &viper_domains,
            &[],
            &viper_functions,
            &viper_predicates,
            &viper_methods,
        )
    }
}
