use super::*;
use viper;
use viper::AstFactory;
use prusti_interface::config;

#[derive(Debug)]
pub struct Program {
    pub fields: Vec<Field>,
    pub builtin_methods: Vec<BodylessMethod>,
    pub methods: Vec<CfgMethod>,
    pub functions: Vec<Function>,
    pub viper_predicates: Vec<Predicate>,
}

impl Program {
    pub fn to_viper<'v>(self, ast: &AstFactory<'v>) -> viper::Program<'v> {
        let domains: Vec<viper::Domain> = vec![];
        let fields = self.fields.to_viper(ast);
        let mut methods = self.methods;
        let mut functions = self.functions;
        if config::simplify_encoding() {
            let (new_methods, new_functions) = optimisations::functions::inline_constant_functions(
                methods, functions);
            methods = new_methods
                .into_iter()
                .map(|m| {
                    let purified = optimisations::methods::purify_vars(m);
                    optimisations::folding::FoldingOptimiser::optimise(purified)
                })
                .collect();
            functions = new_functions
                .into_iter()
                .map(|f| {
                    optimisations::folding::FoldingOptimiser::optimise(f)
                })
                .collect();
        }
        let mut viper_functions: Vec<_> = functions.into_iter().map(|f| f.to_viper(ast)).collect();
        let mut viper_methods: Vec<_> = methods.into_iter().map(|m| m.to_viper(ast)).collect();
        viper_methods.extend(self.builtin_methods.into_iter().map(|m| m.to_viper(ast)));
        let mut predicates = self.viper_predicates.to_viper(ast);
        if config::verify_only_preamble() {
            viper_methods = Vec::new();
        }

        info!(
            "Viper encoding uses {} domains, {} fields, {} functions, {} predicates, {} methods",
            domains.len(), fields.len(), viper_functions.len(), predicates.len(),
            viper_methods.len()
        );

        // Add a function that represents the symbolic read permission amount.
        viper_functions.push(ast.function(
            "read$",
            &[],
            ast.perm_type(),
            &[],
            &[
                ast.lt_cmp(ast.no_perm(), ast.result(ast.perm_type())),
                ast.lt_cmp(ast.result(ast.perm_type()), ast.full_perm()),
            ],
            ast.no_position(),
            None,
        ));

        // Add a predicate that represents the dead loan token.
        predicates.push(
            ast.predicate(
                "DeadBorrowToken$",
                &[LocalVar {
                    name: "borrow".to_string(),
                    typ: Type::Int,
                }
                    .to_viper_decl(ast)],
                None,
            ),
        );

        ast.program(&domains, &fields, &viper_functions, &predicates, &viper_methods)
    }
}
