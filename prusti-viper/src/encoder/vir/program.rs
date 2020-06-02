use super::*;
use prusti_common::config;
use viper::{self, AstFactory};

#[derive(Debug, Serialize, Deserialize)]
pub struct Program {
    pub fields: Vec<Field>,
    pub builtin_methods: Vec<BodylessMethod>,
    pub methods: Vec<CfgMethod>,
    pub functions: Vec<Function>,
    pub viper_predicates: Vec<Predicate>,
}

impl Program {
    pub fn optimized(mut self) -> Self {
        // can't borrow self because we need to move fields
        let (new_methods, new_functions) =
            optimizations::functions::inline_constant_functions(self.methods, self.functions);
        self.methods = new_methods
            .into_iter()
            .map(|m| {
                let purified = optimizations::methods::purify_vars(m);
                optimizations::folding::FoldingOptimizer::optimize(purified)
            })
            .collect();
        self.functions = new_functions
            .into_iter()
            .map(|f| optimizations::folding::FoldingOptimizer::optimize(f))
            .collect();
        self
    }

    pub fn to_viper<'v>(self, ast: &AstFactory<'v>) -> viper::Program<'v> {
        let domains: Vec<viper::Domain> = vec![];
        let fields = self.fields.to_viper(ast);

        let mut viper_methods: Vec<_> = self.methods.into_iter().map(|m| m.to_viper(ast)).collect();
        viper_methods.extend(self.builtin_methods.into_iter().map(|m| m.to_viper(ast)));
        if config::verify_only_preamble() {
            viper_methods = Vec::new();
        }

        let mut viper_functions: Vec<_> = self
            .functions
            .into_iter()
            .map(|f| f.to_viper(ast))
            .collect();
        let mut predicates = self.viper_predicates.to_viper(ast);

        info!(
            "Viper encoding uses {} domains, {} fields, {} functions, {} predicates, {} methods",
            domains.len(),
            fields.len(),
            viper_functions.len(),
            predicates.len(),
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

        ast.program(
            &domains,
            &fields,
            &viper_functions,
            &predicates,
            &viper_methods,
        )
    }
}
